import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog
import tkinter.font as tkFont
import threading
import json
import os
import sys
import subprocess
import time
import re
import tempfile
import atexit
import webbrowser
from queue import Queue
import yt_dlp
import logging
import concurrent.futures
from threading import Semaphore

# --- yt-dlp Logger Class ---
class YtDlpLogger:
    """Custom logger for yt-dlp that integrates with the application's logging system."""
    
    def __init__(self, app_instance):
        self.app = app_instance
    
    def debug(self, msg):
        """Handle yt-dlp debug messages."""
        self._queue_message(msg, "DEBUG")
    
    def info(self, msg):
        """Handle yt-dlp info messages."""
        self._queue_message(msg, "INFO")
    
    def warning(self, msg):
        """Handle yt-dlp warning messages."""
        self._queue_message(msg, "WARNING")
        
        # Check for SABR indicators in real-time
        self._check_sabr_indicators(msg)
    
    def error(self, msg):
        """Handle yt-dlp error messages."""
        self._queue_message(msg, "ERROR")
    
    def _queue_message(self, msg, level):
        """Queue a message for thread-safe processing on the GUI thread."""
        try:
            # Check for stop request during any yt-dlp operation - be very aggressive
            if self.app.stop_event.is_set():
                elapsed_time = time.time() - getattr(self.app, '_stop_start_time', time.time())
                self.app.log_message(f"LOGGER: Stop detected during yt-dlp operation after {elapsed_time:.1f}s, raising cancellation", "WARNING")
                raise yt_dlp.utils.DownloadCancelled('User requested stop during extraction')
            
            # Also check if we have a download cancellation flag
            if hasattr(self.app, '_current_download_cancelled') and getattr(self.app, '_current_download_cancelled', False):
                self.app.log_message("LOGGER: Download cancellation flag detected, raising cancellation", "WARNING")
                raise yt_dlp.utils.DownloadCancelled('Download cancelled by monitor')
            
            message_data = {
                'message': f"[yt-dlp] {msg}",
                'level': level,
                'timestamp': time.time()
            }
            self.app.message_queue.put_nowait(message_data)
        except yt_dlp.utils.DownloadCancelled:
            # Re-raise cancellation exceptions
            raise
        except Exception:
            # If queue is full or there's an error, silently ignore to prevent blocking
            pass
    
    def _check_sabr_indicators(self, msg):
        """Check if a yt-dlp message indicates SABR restrictions."""
        try:
            msg_lower = msg.lower()
            sabr_indicators = [
                'require a gvs po token',
                'android client https formats require a gvs po token',
                'ios client https formats require a gvs po token',
                'android client sabr formats require',
                'ios client sabr formats require',
                'sabr formats require a gvs po token'
            ]
            
            for indicator in sabr_indicators:
                if indicator in msg_lower:
                    # SABR detected! Trigger detection if not already in SABR mode
                    if not self.app.sabr_mode_active:
                        print(f"SABR detected from yt-dlp warning: {indicator}")
                        # Schedule SABR activation on main thread
                        try:
                            self.app.root.after(0, self.app.activate_sabr_from_warning, msg)
                        except:
                            pass  # Ignore if GUI not available
                    break
        except:
            pass  # Ignore errors in SABR detection

# --- Configuration ---
SETTINGS_FILE = 'settings.json'
DEFAULT_DOWNLOAD_PATH = os.path.join(os.path.expanduser('~'), 'Downloads')

class YouTubeDownloaderApp:
    """
    A GUI application for downloading YouTube videos and playlists using yt-dlp.
    """
    def __init__(self, root):
        self.root = root
        self.root.title("YouTube Video Downloader")
        self.root.geometry("800x700")
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        # --- State Variables ---
        self.download_queue = []
        self.download_thread = None
        self.is_downloading = False
        self.stop_event = threading.Event()
        self.progress_queue = Queue()
        self.message_queue = Queue()  # Queue for yt-dlp messages
        self.is_updating_from_selection = False # Flag to prevent update loops
        self.ydl_process = None  # Store yt-dlp process for stopping
        self.sort_column = None
        self.sort_reverse = False
        self.last_progress_time = 0  # Track last progress update time
        self.stop_message_logged = False  # Flag to prevent repeated stop messages
        self._save_settings_after_id = None  # For delayed save operations
        
        # --- Caching Infrastructure ---
        self.info_cache = {}  # Cache extracted info
        self.extraction_locks = {}  # Prevent concurrent extractions of same URL
        self.cache_expiry = {}  # Track cache expiration times
        
        # --- Batch Processing Infrastructure ---
        self.extraction_semaphore = Semaphore(5)  # Limit concurrent extractions
        
        # --- SABR Bypass Mode Infrastructure ---
        self.sabr_mode_active = False
        self.sabr_detection_details = {}
        self.last_sabr_check = None
        self.sabr_indicator_frame = None
        self.original_quality_options = ['Best', '2160p (4K)', '1440p (2K)', '1080p', '720p', '480p', '360p', '240p', '144p', 'Lowest']
        self.original_audio_options = [
            'default (Auto)', 
            'best (Highest Quality)', 
            'lowest (Smallest Size)',
            'low_webm (~48kbps Opus)', 
            'medium_webm (~70kbps Opus)', 
            'standard_webm (~128kbps Opus)',
            'standard_m4a (~128kbps AAC)', 
            'standard_mp3 (~192kbps MP3)', 
            'high_m4a (~160kbps AAC)'
        ]
        self.sabr_quality_options = ['360p']  # Only 360p works under SABR restrictions
        self.sabr_audio_options = ['standard_mp3 (~192kbps MP3)', 'high_m4a (~160kbps AAC)']

        # --- Cookie Authentication State ---
        self.cookie_browsers = ['chrome', 'firefox', 'edge', 'brave', 'opera', 'vivaldi', 'chromium', 'whale', 'safari']

        # --- GUI Variables ---
        self.download_path = tk.StringVar(value=DEFAULT_DOWNLOAD_PATH)
        self.log_level_var = tk.StringVar(value='INFO')
        self.yt_dlp_debug_var = tk.BooleanVar(value=False)
        self.console_visible_var = tk.BooleanVar(value=True)
        
        # Cookie GUI variables
        self.cookie_mode = tk.StringVar(value='none')
        self.cookie_browser = tk.StringVar(value='chrome')
        self.cookie_browser_profile = tk.StringVar(value='')
        self.cookie_file_path = tk.StringVar(value='')
        
        # --- yt-dlp Logger ---
        self.yt_dlp_logger = YtDlpLogger(self)

        # --- GUI Setup ---
        self.setup_gui()
        self.load_settings()
        self.process_progress_queue()
        self.process_message_queue()
        
        # Start periodic cache cleanup
        self.root.after(300000, self.periodic_cleanup)  # Start cleanup after 5 minutes

    def setup_gui(self):
        """Creates and arranges all the GUI widgets."""
        # --- Main Frames ---
        top_frame = ttk.Frame(self.root, padding="10")
        top_frame.pack(fill=tk.X, side=tk.TOP)

        list_frame = ttk.Frame(self.root, padding="10")
        list_frame.pack(fill=tk.BOTH, expand=True)

        console_frame = ttk.Frame(self.root, padding="10")
        console_frame.pack(fill=tk.X, side=tk.BOTTOM)

        # --- Top Frame: URL Input and Controls ---
        ttk.Label(top_frame, text="YouTube URL:").grid(row=0, column=0, padx=(0, 5), sticky='w')
        self.url_entry = ttk.Entry(top_frame, width=60)
        self.url_entry.grid(row=0, column=1, sticky='ew')
        
        self.add_button = ttk.Button(top_frame, text="Add", command=self.add_url)
        self.add_button.grid(row=0, column=2, padx=5)
        
        top_frame.grid_columnconfigure(1, weight=1)

        # --- Options Frame: Quality and Audio-Only ---
        options_frame = ttk.Frame(top_frame)
        options_frame.grid(row=1, column=1, sticky='w', pady=5)
        
        ttk.Label(options_frame, text="Quality:").pack(side=tk.LEFT, padx=(0, 5))
        self.quality_var = tk.StringVar(value='1080p')
        quality_options = ['Best', '2160p (4K)', '1440p (2K)', '1080p', '720p', '480p', '360p', '240p', '144p', 'Lowest']
        self.quality_menu = ttk.OptionMenu(options_frame, self.quality_var, quality_options[3], *quality_options)  # Default to 1080p
        self.quality_menu.pack(side=tk.LEFT, padx=(0, 20))
        
        self.audio_only_var = tk.BooleanVar()
        self.audio_only_check = ttk.Checkbutton(options_frame, text="Audio Only", variable=self.audio_only_var, command=self.on_audio_only_change)
        self.audio_only_check.pack(side=tk.LEFT)
        
        # Audio format dropdown (initially hidden)
        self.audio_format_var = tk.StringVar(value='default')
        self.audio_format_options = [
            'default (Auto)', 
            'best (Highest Quality)', 
            'lowest (Smallest Size)',
            'low_webm (~48kbps Opus)', 
            'medium_webm (~70kbps Opus)', 
            'standard_webm (~128kbps Opus)',
            'standard_m4a (~128kbps AAC)', 
            'standard_mp3 (~192kbps MP3)', 
            'high_m4a (~160kbps AAC)'
        ]
        self.audio_format_menu = ttk.OptionMenu(options_frame, self.audio_format_var, self.audio_format_options[0], *self.audio_format_options)
        self.audio_format_menu.pack(side=tk.LEFT, padx=(5, 0))
        self.audio_format_menu.pack_forget()  # Hide initially
        
        # Info text about settings applying to selected and new items
        ttk.Label(options_frame, text="Works on selected as well as on new", font=("Arial", 8), foreground="gray").pack(side=tk.LEFT, padx=(20, 0))
        
        # Check FFmpeg availability and update audio options
        self.check_ffmpeg_availability()
        
        self.quality_var.trace_add('write', self.on_setting_change)
        self.audio_format_var.trace_add('write', self.on_setting_change)

        # --- Download Path Frame ---
        path_frame = ttk.Frame(top_frame)
        path_frame.grid(row=2, column=0, columnspan=3, sticky='ew', pady=5)
        ttk.Label(path_frame, text="Download Folder:").pack(side=tk.LEFT, padx=(0, 5))
        self.path_entry = ttk.Entry(path_frame, textvariable=self.download_path, state='readonly')
        self.path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.change_path_button = ttk.Button(path_frame, text="Change...", command=self.change_download_path)
        self.change_path_button.pack(side=tk.LEFT, padx=5)

        # --- Control Buttons Frame ---
        control_frame = ttk.Frame(top_frame)
        control_frame.grid(row=3, column=0, columnspan=3, sticky='w', pady=5)
        
        # Start button with play icon (▶)
        self.start_button = ttk.Button(control_frame, text="▶", command=self.start_download, width=3)
        self.start_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # Stop button with stop icon (⏹)
        self.stop_button = ttk.Button(control_frame, text="⏹", command=self.stop_download, state=tk.DISABLED, width=3)
        self.stop_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # Divider
        ttk.Label(control_frame, text="|", foreground="gray").pack(side=tk.LEFT, padx=(0, 10))
        
        # Move Up button with up arrow (↑)
        self.move_up_button = ttk.Button(control_frame, text="↑", command=self.move_up, width=3)
        self.move_up_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # Move Down button with down arrow (↓)
        self.move_down_button = ttk.Button(control_frame, text="↓", command=self.move_down, width=3)
        self.move_down_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # Add To Top button with underline and up arrow (⎺↑)
        self.add_to_top_button = ttk.Button(control_frame, text="⎺↑", command=self.move_to_top, width=3)
        self.add_to_top_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # Add To Bottom button with overline and down arrow (⎽↓)
        self.add_to_bottom_button = ttk.Button(control_frame, text="⎽↓", command=self.move_to_bottom, width=3)
        self.add_to_bottom_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # Divider
        ttk.Label(control_frame, text="|", foreground="gray").pack(side=tk.LEFT, padx=(0, 10))
        
        # Reset button with circular arrow (↻)
        self.reset_button = ttk.Button(control_frame, text="↻", command=self.reset_selected, state=tk.DISABLED, width=3)
        self.reset_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # Divider
        ttk.Label(control_frame, text="|", foreground="gray").pack(side=tk.LEFT, padx=(0, 10))
        
        # Remove Selected button
        self.remove_button = ttk.Button(control_frame, text="Remove Selected", command=self.remove_selected)
        self.remove_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # Clear All button
        self.clear_all_button = ttk.Button(control_frame, text="Clear All", command=self.clear_all)
        self.clear_all_button.pack(side=tk.LEFT)

        # --- SABR Control Frame (new line under control buttons) ---
        sabr_control_frame = ttk.Frame(top_frame)
        sabr_control_frame.grid(row=4, column=0, columnspan=3, sticky='w', pady=5)
        
        # Manual SABR Check button
        self.manual_sabr_button = ttk.Button(sabr_control_frame, text="Check SABR", command=self.manual_sabr_check)
        self.manual_sabr_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # Force SABR Mode button
        self.force_sabr_button = ttk.Button(sabr_control_frame, text="Force SABR", command=self.force_sabr_mode)
        self.force_sabr_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # SABR indicator will be added here dynamically when active
        self.sabr_control_frame = sabr_control_frame

        # --- Cookie Authentication Frame (row 5 under SABR controls) ---
        cookie_frame = ttk.Frame(top_frame)
        cookie_frame.grid(row=5, column=0, columnspan=3, sticky='ew', pady=5)
        
        ttk.Label(cookie_frame, text="🍪 Cookies:").pack(side=tk.LEFT, padx=(0, 2))
        
        # Help button for cookie setup guidance
        cookie_help_btn = tk.Button(cookie_frame, text="?", font=("Arial", 7, "bold"),
                                     width=2, height=1, relief='groove', cursor='hand2',
                                     command=self.show_cookie_help)
        cookie_help_btn.pack(side=tk.LEFT, padx=(0, 5))
        
        # Mode dropdown: None / From Browser / From File
        cookie_modes = ['None', 'From Browser', 'From File']
        self.cookie_mode_menu = ttk.OptionMenu(cookie_frame, self.cookie_mode, 'none',
                                               *[m.lower().replace(' ', '_') for m in cookie_modes])
        # Override with user-friendly labels
        menu = self.cookie_mode_menu['menu']
        menu.delete(0, 'end')
        mode_map = [('none', 'None'), ('from_browser', 'From Browser'), ('from_file', 'From File')]
        for val, label in mode_map:
            menu.add_command(label=label, command=lambda v=val: self._set_cookie_mode(v))
        self.cookie_mode_menu.pack(side=tk.LEFT, padx=(0, 10))
        
        # --- Browser sub-widgets (shown when mode = from_browser) ---
        self.cookie_browser_frame = ttk.Frame(cookie_frame)
        
        ttk.Label(self.cookie_browser_frame, text="Browser:").pack(side=tk.LEFT, padx=(0, 3))
        self.cookie_browser_menu = ttk.OptionMenu(self.cookie_browser_frame, self.cookie_browser,
                                                   'chrome', *self.cookie_browsers)
        self.cookie_browser_menu.pack(side=tk.LEFT, padx=(0, 8))
        
        ttk.Label(self.cookie_browser_frame, text="Profile:").pack(side=tk.LEFT, padx=(0, 3))
        self.cookie_profile_entry = ttk.Entry(self.cookie_browser_frame, textvariable=self.cookie_browser_profile, width=14)
        self.cookie_profile_entry.pack(side=tk.LEFT, padx=(0, 8))
        
        self.cookie_browser_warning = tk.Label(self.cookie_browser_frame, text="⚠ Close browser first!",
                                               font=("Arial", 8, "bold"), fg="orange")
        self.cookie_browser_warning.pack(side=tk.LEFT, padx=(5, 0))
        
        # Test Cookies button
        self.cookie_test_button = ttk.Button(self.cookie_browser_frame, text="Test", 
                                             command=self.test_browser_cookies, width=5)
        self.cookie_test_button.pack(side=tk.LEFT, padx=(8, 0))
        # Hidden initially
        
        # --- File sub-widgets (shown when mode = from_file) ---
        self.cookie_file_frame = ttk.Frame(cookie_frame)
        
        self.cookie_file_entry = ttk.Entry(self.cookie_file_frame, textvariable=self.cookie_file_path, width=40, state='readonly')
        self.cookie_file_entry.pack(side=tk.LEFT, padx=(0, 5))
        
        self.cookie_browse_button = ttk.Button(self.cookie_file_frame, text="Browse...", command=self.browse_cookie_file)
        self.cookie_browse_button.pack(side=tk.LEFT, padx=(0, 8))
        
        tk.Label(self.cookie_file_frame, text="Netscape cookies.txt", font=("Arial", 8), fg="gray").pack(side=tk.LEFT)
        # Hidden initially
        
        # Status label for cookie authentication
        self.cookie_status_label = tk.Label(cookie_frame, text="", font=("Arial", 8), fg="green")
        self.cookie_status_label.pack(side=tk.LEFT, padx=(10, 0))

        # --- List Frame: Download Queue ---
        # Status summary frame with colored labels (above the table)
        status_summary_frame = ttk.Frame(list_frame)
        status_summary_frame.pack(fill=tk.X, pady=(0, 5))
        
        # Individual status labels with colors
        self.total_label = tk.Label(status_summary_frame, text="Total: 0", font=("Arial", 9, "bold"), fg="black")
        self.total_label.pack(side=tk.LEFT, padx=(5, 10))
        
        self.done_label = tk.Label(status_summary_frame, text="Done: 0", font=("Arial", 9, "bold"), fg="green")
        self.done_label.pack(side=tk.LEFT, padx=(0, 10))
        
        self.pending_label = tk.Label(status_summary_frame, text="Pending: 0", font=("Arial", 9, "bold"), fg="black")
        self.pending_label.pack(side=tk.LEFT, padx=(0, 10))
        
        self.failed_label = tk.Label(status_summary_frame, text="Failed: 0", font=("Arial", 9, "bold"), fg="red")
        self.failed_label.pack(side=tk.LEFT, padx=(0, 10))
        
        self.skipped_label = tk.Label(status_summary_frame, text="Skipped: 0", font=("Arial", 9, "bold"), fg="purple")
        self.skipped_label.pack(side=tk.LEFT, padx=(0, 10))
        
        self.quality_blocked_label = tk.Label(status_summary_frame, text="QualityBlocked: 0", font=("Arial", 9, "bold"), fg="orange")
        self.quality_blocked_label.pack(side=tk.LEFT, padx=(0, 10))
        
        self.age_restricted_label = tk.Label(status_summary_frame, text="AgeRestricted: 0", font=("Arial", 9, "bold"), fg="brown")
        self.age_restricted_label.pack(side=tk.LEFT, padx=(0, 10))
        
        self.downloading_label = tk.Label(status_summary_frame, text="Downloading: 0", font=("Arial", 9, "bold"), fg="blue")
        self.downloading_label.pack(side=tk.LEFT)
        
        # Create a frame for the treeview with line numbers
        tree_container = ttk.Frame(list_frame)
        tree_container.pack(fill=tk.BOTH, expand=True)
        
        # Create frames for line numbers and treeview
        left_line_frame = ttk.Frame(tree_container, width=40)
        left_line_frame.pack(side=tk.LEFT, fill=tk.Y)
        left_line_frame.pack_propagate(False)  # Maintain fixed width
        
        tree_frame = ttk.Frame(tree_container)
        tree_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        right_line_frame = ttk.Frame(tree_container, width=40)
        right_line_frame.pack(side=tk.RIGHT, fill=tk.Y)
        right_line_frame.pack_propagate(False)  # Maintain fixed width
        
        # Create line number labels containers
        self.left_line_labels = []
        self.right_line_labels = []
        
        # Create scrollable frame for left line numbers
        self.left_line_canvas = tk.Canvas(left_line_frame, width=40, bg='lightgray')
        self.left_line_canvas.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollable frame for right line numbers  
        self.right_line_canvas = tk.Canvas(right_line_frame, width=40, bg='lightgray')
        self.right_line_canvas.pack(fill=tk.BOTH, expand=True)
        
        self.tree = ttk.Treeview(tree_frame, columns=('ID', 'Name', 'Quality', 'Duration', 'Status'), show='headings')
        self.tree.heading('ID', text='Video ID', command=lambda: self.sort_treeview('ID'))
        self.tree.heading('Name', text='Video Title', command=lambda: self.sort_treeview('Name'))
        self.tree.heading('Quality', text='Format', command=lambda: self.sort_treeview('Quality'))
        self.tree.heading('Duration', text='Duration', command=lambda: self.sort_treeview('Duration'))
        self.tree.heading('Status', text='Status', command=lambda: self.sort_treeview('Status'))
        self.tree.column('ID', width=120)
        self.tree.column('Name', width=300)
        self.tree.column('Quality', width=100, anchor='center')
        self.tree.column('Duration', width=80, anchor='center')
        self.tree.column('Status', width=100, anchor='center')
        self.tree.bind('<<TreeviewSelect>>', self.on_video_select)
        self.tree.bind('<Button-1>', self.on_tree_click)  # Handle mouse clicks
        self.tree.bind('<Button-3>', self.on_right_click)  # Handle right-click for context menu
        self.tree.bind('<Motion>', self.on_tree_motion)  # Handle mouse motion for cursor changes
        self.tree.bind('<Enter>', self.on_tree_enter)  # Handle mouse enter
        self.tree.bind('<Leave>', self.on_tree_leave)  # Handle mouse leave
        
        # Configure status colors
        self.setup_status_colors()
        
        # Scrollbar for the treeview with synchronized line numbers
        tree_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.on_tree_scroll)
        self.tree.configure(yscroll=self.on_tree_scrollbar_set)
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)



        # --- Console Frame: Progress Output ---
        console_header_frame = ttk.Frame(console_frame)
        console_header_frame.pack(fill=tk.X, pady=(0, 5))
        
        # Console visibility checkbox
        self.console_check = ttk.Checkbutton(console_header_frame, text="Console", 
                                           variable=self.console_visible_var, command=self.on_console_visibility_change)
        self.console_check.pack(side=tk.LEFT)
        
        # Log level dropdown - moved to left side
        log_level_frame = ttk.Frame(console_header_frame)
        log_level_frame.pack(side=tk.LEFT, padx=(20, 0))
        
        ttk.Label(log_level_frame, text="Log Level:").pack(side=tk.LEFT, padx=(0, 5))
        log_levels = ['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL']
        self.log_level_menu = ttk.OptionMenu(log_level_frame, self.log_level_var, 'INFO', *log_levels, command=self.on_log_level_change)
        self.log_level_menu.pack(side=tk.LEFT)
        
        # yt-dlp debug checkbox
        self.yt_dlp_debug_check = ttk.Checkbutton(console_header_frame, text="Show yt-dlp debug output", 
                                                  variable=self.yt_dlp_debug_var, command=self.on_yt_dlp_debug_change)
        self.yt_dlp_debug_check.pack(side=tk.LEFT, padx=(20, 0))
        
        # Check Dependencies button
        self.check_deps_button = ttk.Button(console_header_frame, text="Check Dependencies", command=self.check_dependencies)
        self.check_deps_button.pack(side=tk.LEFT, padx=(20, 0))
        
        # Clear Logs button
        self.clear_logs_button = ttk.Button(console_header_frame, text="Clear Logs", command=self.clear_logs)
        self.clear_logs_button.pack(side=tk.LEFT, padx=(10, 0))
        

        
        self.console = scrolledtext.ScrolledText(console_frame, height=14, state=tk.DISABLED, bg='black', fg='white', font=("Courier", 9))
        self.console.pack(fill=tk.X, expand=True)
        


    def setup_status_colors(self):
        """Configure treeview tags for status colors."""
        self.tree.tag_configure('pending', foreground='black')
        self.tree.tag_configure('downloading', foreground='blue')
        self.tree.tag_configure('done', foreground='green')
        self.tree.tag_configure('failed', foreground='red')
        self.tree.tag_configure('skipped', foreground='purple')
        self.tree.tag_configure('qualityblocked', foreground='orange')
        self.tree.tag_configure('agerestricted', foreground='brown')
        self.tree.tag_configure('hover', background='lightgray')
        self.tree.tag_configure('current_item', background='lightgreen')
        
        # Track current hover item
        self.current_hover_item = None

    def update_line_numbers(self):
        """Updates line numbers and highlights currently downloading item."""
        # Clear existing line numbers
        self.left_line_canvas.delete("all")
        self.right_line_canvas.delete("all")
        
        # Get all items in the treeview
        all_items = self.tree.get_children()
        
        if not all_items:
            # Handle empty queue state gracefully
            self.left_line_canvas.configure(scrollregion=(0, 0, 0, 0))
            self.right_line_canvas.configure(scrollregion=(0, 0, 0, 0))
            return
        
        # Calculate proper row height and header offset
        try:
            # Get the actual row height from treeview
            sample_bbox = self.tree.bbox(all_items[0])
            if sample_bbox:
                row_height = sample_bbox[3]  # Height of the row
                header_height = sample_bbox[1]  # Y position of first row (header offset)
            else:
                row_height = 20  # Fallback height
                header_height = 20  # Fallback header height
        except:
            row_height = 20  # Fallback height
            header_height = 20  # Fallback header height
        
        # Find currently downloading item
        downloading_item_index = -1
        for i, item_id in enumerate(all_items):
            current_values = self.tree.item(item_id, 'values')
            if len(current_values) >= 5 and current_values[4] == '↓ Downloading':
                downloading_item_index = i
                break
        
        # If no item is downloading, highlight the first pending item
        if downloading_item_index == -1:
            for i, item_id in enumerate(all_items):
                current_values = self.tree.item(item_id, 'values')
                if len(current_values) >= 5 and current_values[4] == 'Pending':
                    downloading_item_index = i
                    break
        
        # Remove current_item tag from all items first
        for item_id in all_items:
            current_tags = list(self.tree.item(item_id, 'tags'))
            if 'current_item' in current_tags:
                current_tags.remove('current_item')
                self.tree.item(item_id, tags=current_tags)
        
        # Create line numbers for each item
        for i, item_id in enumerate(all_items):
            line_num = i + 1
            y_pos = header_height + (i * row_height) + (row_height // 2)  # Account for header and center in row
            
            # Check if this is the current/downloading item
            is_current = (i == downloading_item_index)
            
            # Left line numbers
            if is_current:
                left_text = f"> {line_num}"
                self.left_line_canvas.create_text(20, y_pos, text=left_text, anchor="center", 
                                                fill="darkgreen", font=("Arial", 9, "bold"))
            else:
                self.left_line_canvas.create_text(20, y_pos, text=str(line_num), anchor="center", 
                                                fill="gray", font=("Arial", 9))
            
            # Right line numbers  
            if is_current:
                right_text = f"{line_num} <"
                self.right_line_canvas.create_text(20, y_pos, text=right_text, anchor="center", 
                                                 fill="darkgreen", font=("Arial", 9, "bold"))
            else:
                self.right_line_canvas.create_text(20, y_pos, text=str(line_num), anchor="center", 
                                                 fill="gray", font=("Arial", 9))
        
        # Update canvas scroll region to match the content height
        total_height = header_height + (len(all_items) * row_height)
        self.left_line_canvas.configure(scrollregion=(0, 0, 40, total_height))
        self.right_line_canvas.configure(scrollregion=(0, 0, 40, total_height))
        
        # Highlight current item with light green background
        if downloading_item_index >= 0 and downloading_item_index < len(all_items):
            current_item = all_items[downloading_item_index]
            current_tags = list(self.tree.item(current_item, 'tags'))
            # Add current_item tag if not already present
            if 'current_item' not in current_tags:
                current_tags.append('current_item')
                self.tree.item(current_item, tags=current_tags)

    def on_tree_scroll(self, *args):
        """Handle treeview scrolling and synchronize line numbers."""
        self.tree.yview(*args)
        # Synchronize line number canvases
        self.left_line_canvas.yview(*args)
        self.right_line_canvas.yview(*args)

    def on_tree_scrollbar_set(self, first, last):
        """Handle scrollbar updates and synchronize line numbers."""
        # Update the scrollbar
        tree_scrollbar = None
        for child in self.tree.master.winfo_children():
            if isinstance(child, ttk.Scrollbar):
                tree_scrollbar = child
                break
        if tree_scrollbar:
            tree_scrollbar.set(first, last)
        
        # Synchronize line number canvases
        self.left_line_canvas.yview_moveto(first)
        self.right_line_canvas.yview_moveto(first)

    def format_video_id_with_icon(self, video_id):
        """Format Video ID with link icon if it's clickable."""
        if video_id and video_id != 'N/A' and self.is_valid_video_id(video_id):
            return f"🔗 {video_id}"
        else:
            return video_id or 'N/A'
    
    def is_valid_video_id(self, video_id):
        """Check if a Video ID appears to be valid for YouTube."""
        if not video_id or video_id == 'N/A':
            return False
        # YouTube Video IDs are typically 11 characters long and contain alphanumeric characters, hyphens, and underscores
        import re
        return bool(re.match(r'^[a-zA-Z0-9_-]{11}$', video_id))
    
    def open_video_in_browser(self, video_id):
        """Open a YouTube video in the default browser with enhanced error handling."""
        if not video_id or video_id == 'N/A':
            self.log_message("Cannot open video: Invalid Video ID", "WARNING")
            return False
        
        youtube_url = f"https://www.youtube.com/watch?v={video_id}"
        try:
            webbrowser.open(youtube_url)
            self.log_message(f"Opened YouTube video: {video_id}")
            return True
        except Exception as e:
            self.log_message(f"Failed to open browser for video {video_id}: {e}", "ERROR")
            return False

    def change_download_path(self):
        """Opens a dialog to choose a new download directory."""
        new_path = filedialog.askdirectory(title="Select Download Folder", initialdir=self.download_path.get())
        if new_path:
            self.download_path.set(new_path)
            self.log_message(f"Download path set to: {new_path}")
            self.schedule_save_settings()

    def on_video_select(self, event):
        """Updates quality controls when a video is selected in the list."""
        if self.url_entry.get().strip(): # Do nothing if user is typing a new URL
            return
            
        selected_items = self.tree.selection()
        if not selected_items:
            return

        item_id = selected_items[0] # Handle only the first selected item
        
        video_info = None
        for v in self.download_queue:
            if v['item_id'] == item_id:
                video_info = v
                break

        if video_info:
            self.is_updating_from_selection = True # Set flag to prevent trace callback
            
            quality = video_info['quality']
            if quality.startswith('Audio-'):
                self.audio_only_var.set(True)
                audio_format = quality.split('-')[1]  # Extract format key
                
                # Map format keys to display names
                format_display_map = {
                    'default': 'default (Auto)',
                    'best': 'best (Highest Quality)',
                    'lowest': 'lowest (Smallest Size)',
                    'low_webm': 'low_webm (~48kbps Opus)',
                    'medium_webm': 'medium_webm (~70kbps Opus)',
                    'standard_webm': 'standard_webm (~128kbps Opus)',
                    'standard_m4a': 'standard_m4a (~128kbps AAC)',
                    'standard_mp3': 'standard_mp3 (~192kbps MP3)',
                    'high_m4a': 'high_m4a (~160kbps AAC)'
                }
                
                display_name = format_display_map.get(audio_format, 'default (Auto)')
                self.audio_format_var.set(display_name)
                self.audio_format_menu.pack(side=tk.LEFT, padx=(5, 0), after=self.audio_only_check)
                self.quality_menu.config(state=tk.DISABLED)
            else:
                self.audio_only_var.set(False)
                self.audio_format_menu.pack_forget()
                self.quality_var.set(quality)
                self.quality_menu.config(state=tk.NORMAL)
            
            self.is_updating_from_selection = False # Unset flag
        
        # Update reset button state and status summary
        self.update_reset_button_state()
        self.update_status_summary()

    def on_tree_click(self, event):
        """Handle mouse clicks on the treeview to detect Video ID column clicks."""
        # Identify what was clicked
        region = self.tree.identify_region(event.x, event.y)
        if region == "cell":
            # Get the column that was clicked
            column = self.tree.identify_column(event.x)
            # Column #1 is the Video ID column (columns are 1-indexed)
            if column == '#1':
                # Get the item that was clicked
                item = self.tree.identify_row(event.y)
                if item:
                    # Get the video ID from the item
                    values = self.tree.item(item, 'values')
                    if len(values) > 0:
                        video_id_display = values[0]  # Video ID display value (may have icon) - back to index 0
                        # Only process clicks on items with the link icon (clickable Video IDs)
                        if video_id_display and video_id_display.startswith('🔗 '):
                            # Extract actual Video ID by removing the icon prefix
                            video_id = video_id_display.replace('🔗 ', '')
                            # Open video in browser using enhanced method
                            self.open_video_in_browser(video_id)

    def on_tree_motion(self, event):
        """Handle mouse motion over treeview to change cursor for Video ID column and handle hover highlighting."""
        # Handle hover highlighting
        item = self.tree.identify_row(event.y)
        if item and item != self.current_hover_item:
            # Remove hover from previous item
            if self.current_hover_item:
                current_tags = list(self.tree.item(self.current_hover_item, 'tags'))
                if 'hover' in current_tags:
                    current_tags.remove('hover')
                    self.tree.item(self.current_hover_item, tags=current_tags)
            
            # Add hover to new item
            if item:
                current_tags = list(self.tree.item(item, 'tags'))
                if 'hover' not in current_tags:
                    current_tags.append('hover')
                    self.tree.item(item, tags=current_tags)
                self.current_hover_item = item
        
        # Handle cursor changes for Video ID column
        region = self.tree.identify_region(event.x, event.y)
        if region == "cell":
            column = self.tree.identify_column(event.x)
            # Column #1 is the Video ID column
            if column == '#1':
                if item:
                    values = self.tree.item(item, 'values')
                    if len(values) > 0 and values[0] and values[0].startswith('🔗 '):
                        # Change cursor to hand pointer for clickable Video IDs (those with icons)
                        self.tree.config(cursor="hand2")
                        return
        
        # Reset cursor to default for all other areas
        self.tree.config(cursor="")

    def on_tree_enter(self, event):
        """Handle mouse entering the treeview."""
        pass  # Motion handler will take care of hover highlighting

    def on_right_click(self, event):
        """Handle right-click to show context menu for removing selected videos."""
        # Select the item under the cursor if not already selected
        item = self.tree.identify_row(event.y)
        current_selection = self.tree.selection()
        
        if item:
            # If the clicked item is not in the current selection, replace selection with just this item
            # If it's already selected, keep the current selection (supports multi-select)
            if item not in current_selection:
                self.tree.selection_set(item)
            
            # Get updated selection (may include multiple items)
            updated_selection = self.tree.selection()
            num_selected = len(updated_selection)
            
            # Create context menu
            context_menu = tk.Menu(self.root, tearoff=0)
            
            # Show appropriate label based on selection count
            if num_selected == 1:
                context_menu.add_command(label="Remove", command=self.remove_selected)
            else:
                context_menu.add_command(label=f"Remove {num_selected} Selected", command=self.remove_selected)
            
            context_menu.add_separator()
            context_menu.add_command(label="Remove All", command=self.clear_all)
            
            # Show the context menu at the cursor position
            try:
                context_menu.tk_popup(event.x_root, event.y_root)
            finally:
                # Make sure to release the menu on release
                context_menu.grab_release()
        elif current_selection:
            # Right-click on empty space but items are selected - show menu for selected items
            num_selected = len(current_selection)
            context_menu = tk.Menu(self.root, tearoff=0)
            
            if num_selected == 1:
                context_menu.add_command(label="Remove", command=self.remove_selected)
            else:
                context_menu.add_command(label=f"Remove {num_selected} Selected", command=self.remove_selected)
            
            context_menu.add_separator()
            context_menu.add_command(label="Remove All", command=self.clear_all)
            
            try:
                context_menu.tk_popup(event.x_root, event.y_root)
            finally:
                context_menu.grab_release()
        # If no item and no selection, don't show menu (nothing to remove)

    def on_tree_leave(self, event):
        """Handle mouse leaving the treeview."""
        # Remove hover highlighting when mouse leaves
        if self.current_hover_item:
            current_tags = list(self.tree.item(self.current_hover_item, 'tags'))
            if 'hover' in current_tags:
                current_tags.remove('hover')
                self.tree.item(self.current_hover_item, tags=current_tags)
            self.current_hover_item = None

    def on_audio_only_change(self):
        """Handles audio only checkbox changes and shows/hides audio format dropdown."""
        if self.audio_only_var.get():
            # Show audio format dropdown and disable quality dropdown
            self.audio_format_menu.pack(side=tk.LEFT, padx=(5, 0), after=self.audio_only_check)
            self.quality_menu.config(state=tk.DISABLED)
        else:
            # Hide audio format dropdown and enable quality dropdown
            self.audio_format_menu.pack_forget()
            self.quality_menu.config(state=tk.NORMAL)
        self.on_setting_change()

    def on_setting_change(self, *args):
        """Updates a selected video's settings when controls are changed."""
        if self.is_updating_from_selection: # Do nothing if change was triggered by selection
            return
            
        selected_items = self.tree.selection()
        if not selected_items:
            return

        if self.audio_only_var.get():
            audio_format = self.audio_format_var.get()
            # Extract the format key from the display name
            format_key = audio_format.split()[0]  # Extract 'default', 'best', 'standard_mp3', etc.
            new_quality = f'Audio-{format_key}'
        else:
            new_quality = self.quality_var.get()

        for item_id in selected_items:
            # Update internal data
            for video in self.download_queue:
                if video['item_id'] == item_id:
                    video['quality'] = new_quality
                    break
            
            # Update GUI
            current_values = self.tree.item(item_id, 'values')
            status = current_values[4] if len(current_values) > 4 else 'Pending'
            self.tree.item(item_id, values=(current_values[0], current_values[1], new_quality, current_values[3] if len(current_values) > 3 else 'N/A', status))
        
        self.log_message(f"Updated settings for {len(selected_items)} selected item(s).")
        self.schedule_save_settings()

    def on_log_level_change(self, selected_level):
        """Handles log level dropdown changes."""
        self.log_message(f"Log level changed to: {selected_level}")
        self.schedule_save_settings()  # Save the new log level setting

    def on_yt_dlp_debug_change(self):
        """Handles yt-dlp debug checkbox changes."""
        if self.yt_dlp_debug_var.get():
            self.log_message("yt-dlp debug output enabled")
        else:
            self.log_message("yt-dlp debug output disabled")
        self.schedule_save_settings()  # Save the new debug setting

    def on_console_visibility_change(self):
        """Handles console visibility checkbox changes."""
        if self.console_visible_var.get():
            self.console.pack(fill=tk.X, expand=True)
            self.log_message("Console shown")
        else:
            self.console.pack_forget()
        self.schedule_save_settings()  # Save the new console visibility setting

    def clear_logs(self):
        """Clears all messages from the console."""
        self.console.config(state=tk.NORMAL)
        self.console.delete(1.0, tk.END)
        self.console.config(state=tk.DISABLED)
        # Don't log a message about clearing logs since we just cleared them

    def configure_ydl_opts_with_logger(self, ydl_opts):
        """Configure ydl_opts with logger when debug is enabled."""
        if self.yt_dlp_debug_var.get():
            # Enable debug logging
            ydl_opts['logger'] = self.yt_dlp_logger
            ydl_opts['quiet'] = False
            ydl_opts['no_warnings'] = False
        else:
            # Keep quiet mode when debug is disabled
            ydl_opts['quiet'] = True
            ydl_opts['no_warnings'] = True
        
        # Add common performance optimizations
        ydl_opts.update({
            'ignoreerrors': True,
            'writeinfojson': False,
            'writethumbnail': False,
            'writesubtitles': False,
            'writeautomaticsub': False,
            'nocheckcertificate': True,
            'prefer_insecure': False
        })
        
        return ydl_opts

    def build_extractor_args(self):
        """Build unified extractor arguments for consistent YouTube handling.
        
        When cookies are active, android/ios clients are skipped by yt-dlp
        (they don't support cookies). Use cookie-compatible clients instead.
        """
        cookie_mode = getattr(self, 'cookie_mode', None)
        cookies_active = cookie_mode and cookie_mode.get() not in ('', 'none', None)
        
        if cookies_active:
            # Cookie-compatible clients only — android/ios don't support cookies
            return {
                'youtube': {
                    'player_client': ['tv', 'web_safari', 'web'],
                }
            }
        else:
            # Default SABR bypass configuration (no cookies)
            return {
                'youtube': {
                    'player_client': ['android', 'tv', 'ios'],
                    'player_skip': ['webpage', 'configs'],
                    'skip': ['hls', 'dash'],
                    'include_hls_manifest': False,
                    'include_dash_manifest': False
                }
            }

    def get_audio_format_selector(self, quality_option, ffmpeg_available=True):
        """Generate yt-dlp format selector based on audio quality choice with SABR-compatible fallbacks."""
        
        # When cookies are active, HTTPS audio formats also return 403.
        # Use HLS format with bestaudio fallback.
        cookie_mode = getattr(self, 'cookie_mode', None)
        cookies_active = cookie_mode and cookie_mode.get() not in ('', 'none', None)
        
        if cookies_active:
            selected_format = 'bestaudio[protocol=m3u8_native]/bestaudio[protocol=m3u8]/bestaudio/worst'
            self.log_message(f"Audio format selector for '{quality_option}' (HLS/cookie mode): {selected_format}", "DEBUG")
            return selected_format
        
        # Progressive fallback strategy for audio formats due to SABR/PO Token restrictions
        audio_format_map = {
            'default': 'bestaudio/best[height<=480]/best',  # Fallback to low-res video if needed
            'lowest': 'worstaudio/bestaudio/best[height<=360]/best',
            'best': 'bestaudio/best[height<=720]/best',
            'low_webm': 'bestaudio[ext=webm]/bestaudio/best[height<=360]/best',
            'medium_webm': 'bestaudio[ext=webm]/bestaudio/best[height<=480]/best',
            'standard_webm': 'bestaudio[ext=webm]/bestaudio/best[height<=480]/best',
            'standard_m4a': 'bestaudio[ext=m4a]/bestaudio/best[height<=480]/best',
            'standard_mp3': 'bestaudio/best[height<=480]/best',  # + FFmpeg postprocessor
            'high_m4a': 'bestaudio[ext=m4a]/bestaudio/best[height<=720]/best'
        }
        
        # Handle FFmpeg-dependent options
        if quality_option == 'standard_mp3' and not ffmpeg_available:
            self.log_message("MP3 format requires FFmpeg but it's not available. Using default audio format.", "WARNING")
            return 'bestaudio/best[height<=480]/best'
        
        selected_format = audio_format_map.get(quality_option, 'bestaudio/best[height<=480]/best')
        self.log_message(f"Audio format selector for '{quality_option}': {selected_format}", "DEBUG")
        return selected_format

    def get_video_format_selector(self, quality_option):
        """Generate yt-dlp format selector based on video quality choice with SABR-compatible fallbacks.
        
        When cookies are active, HTTPS direct-download formats return 403 (they need
        PO tokens for SABR). Only HLS formats work for cookie-authenticated content.
        We detect this and prefer HLS protocol formats via the 'protocol=m3u8' filter.
        """
        # Clean up quality option (remove extra info in parentheses)
        clean_quality = quality_option.split()[0].lower()
        
        # Check if cookies are active — if so, HTTPS formats will 403
        cookie_mode = getattr(self, 'cookie_mode', None)
        cookies_active = cookie_mode and cookie_mode.get() not in ('', 'none', None)
        
        if cookies_active:
            # HLS-only format selectors for cookie-authenticated content.
            # HTTPS direct formats return 403 without PO tokens; only HLS works.
            height_map = {
                'best': 1080, '1080p': 1080, '720p': 720, '480p': 480,
                '360p': 360, '240p': 240, '144p': 144, 'default': 720,
                '1440p': 1440, '2160p': 2160, '4320p': 4320, 'lowest': 144,
            }
            target = height_map.get(clean_quality, 720)
            # Try: HLS at target quality → any HLS → absolute worst as last resort
            selected_format = (
                f'best[height<={target}][protocol=m3u8_native]/best[height<={target}][protocol=m3u8]/'
                f'best[protocol=m3u8_native]/best[protocol=m3u8]/worst'
            )
            self.log_message(f"Video format selector for '{clean_quality}' (HLS/cookie mode): {selected_format}", "DEBUG")
            return selected_format
        
        # Standard SABR-compatible video format selectors with progressive fallbacks
        video_format_map = {
            'default': 'best[height<=720]/best[height<=480]/best',
            'lowest': 'worst[height>=144]/worst[height>=240]/worst[height>=360]/worst',
            'best': 'best[height<=1080]/best[height<=720]/best',
            '144p': 'best[height<=144]/best[height<=240]/best[height<=360]/best',
            '240p': 'best[height<=240]/best[height<=360]/best',
            '360p': 'best[height<=360]/best[height<=480]/best',
            '480p': 'best[height<=480]/best[height<=720]/best',
            '720p': 'best[height<=720]/best[height<=1080]/best',
            '1080p': 'best[height<=1080]/best[height<=720]/best',
            '1440p': 'best[height<=1440]/best[height<=1080]/best',
            '2160p': 'best[height<=2160]/best[height<=1440]/best',
            '4320p': 'best[height<=4320]/best[height<=2160]/best'
        }
        
        selected_format = video_format_map.get(clean_quality, 'best[height<=720]/best')
        self.log_message(f"Video format selector for '{clean_quality}': {selected_format}", "DEBUG")
        return selected_format

    def get_optimal_format(self, formats, target_quality):
        """Intelligently select the best format based on target quality."""
        if not formats:
            return None
        
        # Quality preference mapping
        quality_map = {
            'Best': float('inf'),
            '1080p': 1080,
            '720p': 720,
            '480p': 480,
            '360p': 360,
            '240p': 240,
            '144p': 144
        }
        
        target_height = quality_map.get(target_quality, 720)
        
        def format_score(fmt):
            height = fmt.get('height', 0)
            vcodec = fmt.get('vcodec', '')
            acodec = fmt.get('acodec', '')
            
            # Prefer formats with both video and audio
            if vcodec == 'none' or acodec == 'none':
                return -1
            
            # Prefer modern codecs
            codec_bonus = 0
            if 'av01' in vcodec:
                codec_bonus = 100
            elif 'vp9' in vcodec:
                codec_bonus = 50
            elif 'h264' in vcodec:
                codec_bonus = 25
            
            # Calculate quality score
            if target_height == float('inf'):
                return height + codec_bonus
            else:
                if height <= target_height:
                    return height + codec_bonus
                else:
                    return height - (height - target_height) * 2 + codec_bonus
        
        # Find best format
        suitable_formats = [f for f in formats if format_score(f) >= 0]
        if suitable_formats:
            return max(suitable_formats, key=format_score)
        
        return formats[0] if formats else None

    def optimize_format_selection(self, info_dict, quality):
        """Optimize format selection process."""
        formats = info_dict.get('formats', [])
        
        if not formats:
            return None
        
        # For audio-only requests
        if quality.startswith('Audio-'):
            audio_formats = [f for f in formats if f.get('vcodec') == 'none']
            if audio_formats:
                return max(audio_formats, key=lambda x: x.get('abr', 0))
        
        # For video requests
        return self.get_optimal_format(formats, quality)

    def setup_postprocessors(self, quality_option):
        """Setup FFmpeg postprocessors for format conversion - ALL audio formats get post-processors."""
        postprocessors = []
        
        # Ensure ALL audio formats use post-processors to extract pure audio files
        if quality_option == 'standard_mp3':
            postprocessors.append({
                'key': 'FFmpegExtractAudio',
                'preferredcodec': 'mp3',
                'preferredquality': '192'
            })
        elif quality_option == 'high_m4a':
            postprocessors.append({
                'key': 'FFmpegExtractAudio',
                'preferredcodec': 'aac',
                'preferredquality': '160'
            })
        else:
            # For all other audio formats, extract audio to ensure pure audio files
            # This prevents video files from being produced when audio is requested
            postprocessors.append({
                'key': 'FFmpegExtractAudio',
                'preferredcodec': 'best',  # Let FFmpeg choose best available codec
                'preferredquality': 'best'
            })
        
        return postprocessors

    def build_download_format(self, video_info):
        """Build format and postprocessors configuration for a video using enhanced quality system."""
        format_opts = {}
        postprocessors = []
        
        if video_info['quality'].startswith('Audio-'):
            # Enhanced audio quality handling with fallback strategy
            audio_format = video_info['quality'].split('-')[1]  # Extract format type
            self.log_message(f"Processing audio download: format='{audio_format}'", "DEBUG")
            
            # Check FFmpeg availability for format-dependent options
            ffmpeg_available = self.check_ffmpeg_availability_status()
            
            # Get format selector using new fallback system
            format_selector = self.get_audio_format_selector(audio_format, ffmpeg_available)
            format_opts['format'] = format_selector
            
            # Add postprocessors if needed for audio extraction/conversion
            postprocessors = self.setup_postprocessors(audio_format)
            
            # For MP3 conversion, add audio extraction options
            if audio_format == 'standard_mp3' and ffmpeg_available:
                postprocessors.append({
                    'key': 'FFmpegExtractAudio',
                    'preferredcodec': 'mp3',
                    'preferredquality': '192'
                })
            
            self.log_message(f"Audio download config: format='{format_selector}', postprocessors={len(postprocessors)}", "DEBUG")
            
        else:
            # Enhanced video quality handling with SABR-compatible fallbacks
            quality = video_info['quality']
            self.log_message(f"Processing video download: quality='{quality}'", "DEBUG")
            
            # Use new video format selector with progressive fallbacks
            format_selector = self.get_video_format_selector(quality.lower())
            format_opts['format'] = format_selector
            format_opts['merge_output_format'] = 'mp4'  # Ensure output is mp4
        
        if postprocessors:
            format_opts['postprocessors'] = postprocessors
            
        return format_opts

    def build_ydl_opts(self, video_info=None, download_path=None, for_download=True):
        """Build unified yt-dlp options for consistent behavior across all operations."""
        # Base options that apply to all operations
        base_opts = {
            'retries': 5,
            'fragment_retries': 5,
            'extractor_retries': 5,
            'socket_timeout': 10,  # Reduced for faster cancellation
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
            },
            'extractor_args': self.build_extractor_args(),
            # Enable Node.js runtime for YouTube nsig (n parameter) challenge solving.
            # Without this, yt-dlp cannot decrypt stream URLs and all formats return 403.
            # Requires: Node.js >= 20 installed + yt-dlp-ejs companion package.
            'js_runtimes': {'node': {}},
        }
        
        if for_download and download_path:
            # Download-specific options
            base_opts.update({
                'outtmpl': os.path.join(download_path, '%(title)s.%(ext)s'),
                'progress_hooks': [self.progress_hook],
                'download_archive': os.path.join(download_path, 'download-archive.txt'),
                'retry_sleep_functions': {'http': lambda n: min(4 ** n, 60)},
                'http_chunk_size': 1048576,  # 1 MiB for faster cancellation
                'concurrent_fragment_downloads': 3,
                'keep_fragments': False,
                'cleanup_fragments': True,
                'noprogress': True,
                'no_color': True,
                'sleep_interval': 0.5,
                'max_sleep_interval': 1,
                'sleep_interval_requests': 0.5,
                # Filename sanitization to prevent filesystem issues
                'restrictfilenames': True,  # Remove problematic characters
                'windowsfilenames': True,   # Windows-safe filenames
            })
            
            # When cookies are active, nsig challenge may fail on older yt-dlp,
            # leaving only HLS formats. Allow download to proceed with those.
            cookie_mode = getattr(self, 'cookie_mode', None)
            if cookie_mode and cookie_mode.get() not in ('', 'none', None):
                base_opts['ignore_no_formats_error'] = True
            
            # Add format-specific options if video_info provided
            if video_info:
                format_opts = self.build_download_format(video_info)
                base_opts.update(format_opts)
        else:
            # Extraction-only options — we want metadata even if format selection
            # fails (e.g. HLS-only streams from cookie-authenticated content).
            # ignore_no_formats_error prevents ignoreerrors from returning None.
            base_opts.update({
                'skip_download': True,
                'ignore_no_formats_error': True,
            })
        
        # Apply cookie authentication if configured
        cookie_opts = self.get_cookie_opts()
        if cookie_opts:
            base_opts.update(cookie_opts)
        
        # Apply logger configuration
        base_opts = self.configure_ydl_opts_with_logger(base_opts)
        
        return base_opts

    # --- Cookie Authentication Methods ---

    # Known DPAPI / App-Bound Encryption error signatures
    _DPAPI_ERROR_PATTERNS = [
        'failed to decrypt with dpapi',
        'could not copy chrome cookie database',
        'failed to load cookies',
        'cookieloaderror',
    ]

    @staticmethod
    def _is_dpapi_error(error_msg):
        """Check if an error message indicates a Chrome DPAPI / App-Bound Encryption failure."""
        msg_lower = str(error_msg).lower()
        return any(pat in msg_lower for pat in YouTubeDownloaderApp._DPAPI_ERROR_PATTERNS)

    def _set_cookie_mode(self, mode):
        """Handle cookie mode changes and show/hide relevant widgets."""
        self.cookie_mode.set(mode)
        # Hide all sub-frames first
        self.cookie_browser_frame.pack_forget()
        self.cookie_file_frame.pack_forget()
        
        if mode == 'from_browser':
            self.cookie_browser_frame.pack(side=tk.LEFT)
            browser = self.cookie_browser.get()
            self.cookie_status_label.config(text=f"Using {browser} cookies (click Test to verify)", fg="#666")
            self.log_message(f"Cookie auth: browser mode ({browser})")
        elif mode == 'from_file':
            self.cookie_file_frame.pack(side=tk.LEFT)
            path = self.cookie_file_path.get()
            if path and os.path.isfile(path):
                self.cookie_status_label.config(text="✓ Cookie file loaded", fg="green")
            else:
                self.cookie_status_label.config(text="Select a cookies.txt file", fg="gray")
            self.log_message("Cookie auth: file mode")
        else:
            self.cookie_status_label.config(text="", fg="green")
            self.log_message("Cookie auth: disabled")
        
        self.schedule_save_settings()

    def test_browser_cookies(self):
        """Test whether browser cookie extraction works (catches DPAPI errors early)."""
        browser = self.cookie_browser.get()
        profile = self.cookie_browser_profile.get().strip() or None
        
        self.cookie_status_label.config(text="Testing...", fg="#666")
        self.cookie_test_button.config(state=tk.DISABLED)
        self.log_message(f"Testing cookie extraction from {browser}...")
        
        def run_test():
            try:
                cookie_tuple = (browser, profile) if profile else (browser,)
                test_opts = {
                    'cookiesfrombrowser': cookie_tuple,
                    'skip_download': True,
                    'quiet': True,
                    'no_warnings': True,
                }
                # Just instantiating YoutubeDL with cookiesfrombrowser triggers cookie loading
                with yt_dlp.YoutubeDL(test_opts) as ydl:
                    pass  # If we get here, cookies loaded successfully
                
                self.root.after(0, lambda: self._on_cookie_test_result(True, browser))
            except Exception as e:
                self.root.after(0, lambda: self._on_cookie_test_result(False, browser, str(e)))
        
        threading.Thread(target=run_test, daemon=True).start()

    def _on_cookie_test_result(self, success, browser, error_msg=''):
        """Handle the result of a cookie extraction test."""
        self.cookie_test_button.config(state=tk.NORMAL)
        
        if success:
            self.cookie_status_label.config(text=f"✓ {browser} cookies OK", fg="green")
            self.log_message(f"Cookie test PASSED: {browser} cookies loaded successfully")
        else:
            if self._is_dpapi_error(error_msg):
                self.cookie_status_label.config(
                    text="✗ DPAPI blocked — use 'From File' instead", fg="red")
                self.log_message(
                    f"Cookie test FAILED: Chrome App-Bound Encryption prevents cookie extraction. "
                    f"This is a known Chrome security change (see github.com/yt-dlp/yt-dlp/issues/10927). "
                    f"Workaround: Install 'Get cookies.txt LOCALLY' browser extension, "
                    f"export cookies as Netscape format, then use 'From File' mode.",
                    "ERROR"
                )
                # Show a helpful messagebox
                messagebox.showwarning(
                    "Chrome Cookie Encryption",
                    "Chrome's App-Bound Encryption prevents external cookie reading.\n\n"
                    "This is a Chrome security feature, not a bug.\n\n"
                    "Workaround:\n"
                    "1. Install 'Get cookies.txt LOCALLY' Chrome extension\n"
                    "2. Go to YouTube and sign in\n"
                    "3. Click the extension icon → Export (Netscape format)\n"
                    "4. Switch to 'From File' mode and select the exported file\n\n"
                    "Alternative: Use Firefox instead (cookies-from-browser works with Firefox)."
                )
            else:
                self.cookie_status_label.config(text=f"✗ Failed: check logs", fg="red")
                self.log_message(f"Cookie test FAILED: {error_msg}", "ERROR")

    def _handle_dpapi_failure(self):
        """Handle DPAPI cookie failure during download — disable broken mode and guide user."""
        if self.cookie_mode.get() == 'from_browser':
            browser = self.cookie_browser.get()
            self.cookie_status_label.config(
                text=f"✗ {browser} DPAPI blocked — use 'From File'", fg="red")
            # Don't auto-switch mode, but warn clearly
            messagebox.showwarning(
                "Cookie Extraction Failed",
                f"Could not read {browser} cookies due to App-Bound Encryption.\n\n"
                "Your download will proceed WITHOUT cookies.\n\n"
                "To fix: switch to 'From File' mode with an exported cookies.txt,\n"
                "or use Firefox as your cookie browser."
            )

    # Chrome Web Store URL for the recommended cookie export extension
    _COOKIE_EXTENSION_URL = (
        "https://chromewebstore.google.com/detail/"
        "get-cookiestxt-locally/cclelndahbckbenkjhflpdbgdldlbecc"
    )

    def show_cookie_help(self):
        """Show a help dialog explaining cookie authentication setup."""
        help_win = tk.Toplevel(self.root)
        help_win.title("Cookie Authentication Help")
        help_win.geometry("580x520")
        help_win.resizable(False, False)
        help_win.transient(self.root)
        help_win.grab_set()

        # Main scrollable frame
        canvas = tk.Canvas(help_win, highlightthickness=0)
        scrollbar = ttk.Scrollbar(help_win, orient="vertical", command=canvas.yview)
        content = ttk.Frame(canvas)

        content.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=content, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=10, pady=10)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Title
        tk.Label(content, text="🍪 Cookie Authentication Guide",
                 font=("Arial", 14, "bold")).pack(anchor="w", pady=(0, 10))

        # Why cookies?
        tk.Label(content, text="Why do I need cookies?",
                 font=("Arial", 11, "bold")).pack(anchor="w", pady=(5, 3))
        tk.Label(content, text=(
            "Cookies are needed to download subscriber-only, members-only,\n"
            "age-restricted, or private videos. They prove to YouTube that\n"
            "you are signed in with a valid account."),
            font=("Arial", 9), justify=tk.LEFT, wraplength=540
        ).pack(anchor="w", padx=(10, 0))

        # Why From Browser fails
        ttk.Separator(content, orient="horizontal").pack(fill=tk.X, pady=10)
        tk.Label(content, text="⚠ Why 'From Browser' fails on Chrome / Edge",
                 font=("Arial", 11, "bold"), fg="#c00").pack(anchor="w", pady=(0, 3))
        tk.Label(content, text=(
            "Since mid-2024, Chrome and Edge use 'App-Bound Encryption' which\n"
            "locks cookies so only Chrome itself can read them. External tools\n"
            "like yt-dlp cannot decrypt them — this is a security feature, not a bug.\n\n"
            "Firefox does NOT have this limitation, so 'From Browser' works\n"
            "fine if you sign into YouTube in Firefox."),
            font=("Arial", 9), justify=tk.LEFT, wraplength=540
        ).pack(anchor="w", padx=(10, 0))

        # Recommended method
        ttk.Separator(content, orient="horizontal").pack(fill=tk.X, pady=10)
        tk.Label(content, text="✅ Recommended: Export cookies with a Chrome extension",
                 font=("Arial", 11, "bold"), fg="#060").pack(anchor="w", pady=(0, 3))

        steps_text = (
            "1.  Install the 'Get cookies.txt LOCALLY' Chrome extension (link below)\n"
            "2.  Go to youtube.com and make sure you're signed in\n"
            "3.  Click the extension icon in Chrome's toolbar\n"
            "4.  Make sure Export Format is set to 'Netscape'\n"
            "5.  Click 'Export' — save the file somewhere easy to find\n"
            "6.  In this app, set Cookies mode to 'From File'\n"
            "7.  Click 'Browse...' and select the exported cookies.txt file"
        )
        tk.Label(content, text=steps_text,
                 font=("Arial", 9), justify=tk.LEFT, wraplength=540
        ).pack(anchor="w", padx=(10, 0))

        # Extension link button
        link_frame = ttk.Frame(content)
        link_frame.pack(anchor="w", padx=(10, 0), pady=(8, 0))

        ext_btn = tk.Button(link_frame, text="📥 Install 'Get cookies.txt LOCALLY' Extension",
                            font=("Arial", 10, "bold"), fg="white", bg="#1a73e8",
                            activebackground="#1558b0", activeforeground="white",
                            cursor="hand2", relief="raised", padx=12, pady=4,
                            command=lambda: webbrowser.open(self._COOKIE_EXTENSION_URL))
        ext_btn.pack(side=tk.LEFT)

        # Security note
        ttk.Separator(content, orient="horizontal").pack(fill=tk.X, pady=10)
        tk.Label(content, text="🔒 Security Notes",
                 font=("Arial", 11, "bold")).pack(anchor="w", pady=(0, 3))
        tk.Label(content, text=(
            "• cookies.txt files contain your active YouTube session — never share them\n"
            "• Cookies expire over time — re-export if downloads start failing\n"
            "• Only use extensions that process cookies locally (not cloud-based)\n"
            "• The recommended extension processes everything in your browser,\n"
            "  no data is sent to external servers"),
            font=("Arial", 9), justify=tk.LEFT, wraplength=540
        ).pack(anchor="w", padx=(10, 0))

        # Close button
        ttk.Button(content, text="Close", command=help_win.destroy).pack(pady=(15, 5))

        # Mouse wheel scrolling
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _on_mousewheel)
        help_win.bind("<Destroy>", lambda e: canvas.unbind_all("<MouseWheel>"))

    def browse_cookie_file(self):
        """Open file dialog to select a Netscape-format cookies.txt file."""
        filepath = filedialog.askopenfilename(
            title="Select Cookies File",
            filetypes=[
                ("Cookie files", "*.txt"),
                ("All files", "*.*")
            ],
            initialdir=os.path.expanduser('~')
        )
        if filepath:
            self.cookie_file_path.set(filepath)
            self.cookie_status_label.config(text="✓ Cookie file loaded", fg="green")
            self.log_message(f"Cookie file selected: {filepath}")
            self.schedule_save_settings()

    def get_cookie_opts(self):
        """Build cookie-related yt-dlp options based on current GUI settings.
        
        The cookie file is passed directly to yt-dlp so it can persist updated
        session tokens. Google/YouTube rotates tokens on each use — if yt-dlp
        can't write them back, the cookies become stale and downloads fail
        with 403 or 'cookies are no longer valid'.
        """
        mode = self.cookie_mode.get()
        if mode == 'from_browser':
            browser = self.cookie_browser.get()
            profile = self.cookie_browser_profile.get().strip() or None
            if profile:
                return {'cookiesfrombrowser': (browser, profile)}
            else:
                return {'cookiesfrombrowser': (browser,)}
        elif mode == 'from_file':
            path = self.cookie_file_path.get().strip()
            if path and os.path.isfile(path):
                self.log_message(f"Using cookie file: {os.path.basename(path)}", "DEBUG")
                return {'cookiefile': path}
            else:
                self.log_message("Cookie file path is invalid or file not found", "WARNING")
        return {}

    def check_dependencies(self):
        """Check yt-dlp and FFmpeg versions manually when button is clicked."""
        self.log_message("Checking dependencies...", "INFO")
        
        # Check yt-dlp version - first try Python import (already imported at top), then CLI
        yt_dlp_found = False
        try:
            # Use the already-imported module (what the app actually uses)
            if hasattr(yt_dlp, 'version') and hasattr(yt_dlp.version, '__version__'):
                current_version = yt_dlp.version.__version__
                self.log_message(f"yt-dlp version: {current_version} (Python module)")
                yt_dlp_found = True
            else:
                # Fallback: try to get version another way
                current_version = getattr(yt_dlp, '__version__', 'unknown')
                if current_version != 'unknown':
                    self.log_message(f"yt-dlp version: {current_version} (Python module)")
                    yt_dlp_found = True
        except (AttributeError, NameError) as e:
            # Module not available or version attribute missing - try CLI
            pass
        except Exception as e:
            self.log_message(f"Error checking yt-dlp Python module: {e}", "DEBUG")
        
        # If Python module not found, try CLI executable
        if not yt_dlp_found:
            try:
                result = subprocess.run(['yt-dlp', '--version'], 
                                      capture_output=True, text=True, timeout=10)
                if result.returncode == 0:
                    current_version = result.stdout.strip()
                    self.log_message(f"yt-dlp version: {current_version} (CLI)")
                    yt_dlp_found = True
            except (FileNotFoundError, subprocess.TimeoutExpired):
                pass  # Will show error below
            except Exception as e:
                self.log_message(f"Error checking yt-dlp CLI: {e}", "DEBUG")
        
        # Check for updates if yt-dlp was found
        if yt_dlp_found:
            try:
                update_result = subprocess.run(['yt-dlp', '--update'], 
                                             capture_output=True, text=True, timeout=30)
                if "Updated yt-dlp" in update_result.stdout:
                    self.log_message("yt-dlp was updated to the latest version", "INFO")
                elif "yt-dlp is up to date" in update_result.stdout:
                    self.log_message("yt-dlp is up to date", "INFO")
                else:
                    self.log_message("yt-dlp update check completed", "INFO")
            except Exception as e:
                self.log_message(f"Could not check for yt-dlp updates: {e}", "DEBUG")
        else:
            self.log_message("yt-dlp not found or not accessible", "WARNING")
            self.log_message("Install with: pip install yt-dlp", "INFO")
        
        # Check FFmpeg version
        try:
            result = subprocess.run(['ffmpeg', '-version'], 
                                  capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                first_line = result.stdout.split('\n')[0]
                if 'ffmpeg version' in first_line.lower():
                    version_info = first_line.split('ffmpeg version')[1].split()[0]
                    self.log_message(f"FFmpeg version: {version_info}")
                else:
                    self.log_message("FFmpeg detected but version format unexpected")
            else:
                self.log_message("FFmpeg not found or not accessible", "WARNING")
                self.log_message("Download from: https://ffmpeg.org/download.html", "INFO")
        except FileNotFoundError:
            self.log_message("FFmpeg not found in system PATH", "WARNING")
            self.log_message("Download from: https://ffmpeg.org/download.html", "INFO")
            self.log_message("For Windows: https://github.com/BtbN/FFmpeg-Builds/releases", "INFO")
        except Exception as e:
            self.log_message(f"Error checking FFmpeg: {e}", "ERROR")
        
        self.log_message("Dependency check complete.", "INFO")
        self.log_message("Note: Using android client to work around YouTube's SABR protocol (2025)", "INFO")
        
        # Refresh audio format options after dependency check
        self.check_ffmpeg_availability()





    def check_ffmpeg_availability(self):
        """Check if FFmpeg is available and update audio format options accordingly."""
        try:
            result = subprocess.run(['ffmpeg', '-version'], 
                                  capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                # FFmpeg is available, keep all options
                self.ffmpeg_available = True
                return
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
        
        # FFmpeg not available, disable FFmpeg-dependent options
        self.ffmpeg_available = False
        self.audio_format_options = [
            'default (Auto)', 
            'best (Highest Quality)', 
            'lowest (Smallest Size)',
            'low_webm (~48kbps Opus)', 
            'medium_webm (~70kbps Opus)', 
            'standard_webm (~128kbps Opus)',
            'standard_m4a (~128kbps AAC)', 
            'high_m4a (~160kbps AAC)'
        ]
        
        # Update the menu
        menu = self.audio_format_menu['menu']
        menu.delete(0, 'end')
        for option in self.audio_format_options:
            menu.add_command(label=option, command=tk._setit(self.audio_format_var, option))
        
        # Reset to available option if currently set to unavailable one
        if 'mp3' in self.audio_format_var.get():
            self.audio_format_var.set('default (Auto)')
            
        self.log_message("FFmpeg not detected. MP3 transcoding disabled. Using native audio formats only.", "INFO")

    def check_ffmpeg_availability_status(self):
        """Return current FFmpeg availability status."""
        return getattr(self, 'ffmpeg_available', False)

    def validate_downloaded_file(self, video_info):
        """Validate that the downloaded file exists and determine actual format/codec."""
        try:
            download_path = self.download_path.get()
            title = video_info['title']
            
            # Create multiple filename variations to check
            filename_variations = []
            
            # 1. Original title (cleaned but with spaces)
            clean_title = re.sub(r'[<>:"/\\|?*？！]', '', title)
            clean_title = re.sub(r'[^\w\s\-_.,()[\]{}]', '', clean_title).strip()
            filename_variations.append(clean_title)
            
            # 2. yt-dlp restricted filename (spaces -> underscores, special chars removed)
            restricted_title = re.sub(r'[^\w\-_.]', '_', title)  # Replace non-alphanumeric with underscore
            restricted_title = re.sub(r'_+', '_', restricted_title)  # Collapse multiple underscores
            restricted_title = restricted_title.strip('_')  # Remove leading/trailing underscores
            filename_variations.append(restricted_title)
            
            # 3. More aggressive cleaning (what yt-dlp might actually create)
            aggressive_title = re.sub(r'[^\w\s]', '', title)  # Remove all special chars
            aggressive_title = re.sub(r'\s+', '_', aggressive_title.strip())  # Spaces to underscores
            filename_variations.append(aggressive_title)
            
            # Determine possible file extensions based on quality
            if video_info['quality'].startswith('Audio-'):
                audio_format = video_info['quality'].split('-')[1]
                if audio_format == 'standard_mp3':
                    possible_extensions = ['.mp3', '.m4a', '.webm', '.aac', '.ogg', '.opus']
                else:
                    possible_extensions = ['.webm', '.m4a', '.aac', '.mp3', '.ogg', '.opus']
            else:
                possible_extensions = ['.mp4', '.webm', '.mkv', '.avi']
            
            # Find the actual downloaded file by checking all variations
            downloaded_file = None
            self.log_message(f"Searching for downloaded file. Variations to check: {filename_variations}", "DEBUG")
            
            for filename in filename_variations:
                for ext in possible_extensions:
                    potential_file = os.path.join(download_path, f"{filename}{ext}")
                    self.log_message(f"Checking: {potential_file}", "DEBUG")
                    if os.path.exists(potential_file):
                        downloaded_file = potential_file
                        self.log_message(f"Found file: {os.path.basename(potential_file)}", "DEBUG")
                        break
                if downloaded_file:
                    break
            
            if not downloaded_file:
                # List actual files in download directory for debugging
                try:
                    actual_files = [f for f in os.listdir(download_path) if os.path.isfile(os.path.join(download_path, f))]
                    self.log_message(f"Download path being checked: {download_path}", "DEBUG")
                    self.log_message(f"Files actually in download directory: {actual_files[:10]}", "DEBUG")  # Show first 10
                    
                    # Look for any video/audio files that might match
                    video_audio_files = [f for f in actual_files if f.lower().endswith(('.mp4', '.webm', '.m4a', '.mp3', '.aac', '.ogg', '.opus'))]
                    if video_audio_files:
                        self.log_message(f"Video/audio files found: {video_audio_files}", "DEBUG")
                        
                        # Try to find a close match using fuzzy matching
                        title_words = set(video_info['title'].lower().split())
                        best_match = None
                        best_score = 0
                        
                        for file in video_audio_files:
                            # Remove extension for comparison
                            file_base = os.path.splitext(file)[0]
                            file_words = set(file_base.lower().replace('_', ' ').replace('-', ' ').split())
                            common_words = title_words.intersection(file_words)
                            score = len(common_words)
                            
                            # Also check if the file contains key parts of the title
                            title_clean = re.sub(r'[^\w\s]', '', video_info['title'].lower())
                            file_clean = re.sub(r'[^\w\s]', '', file_base.lower())
                            
                            # Check for substring matches
                            if title_clean in file_clean or file_clean in title_clean:
                                score += 5  # Bonus for substring match
                            
                            if score > best_score:
                                best_match = file
                                best_score = score
                        
                        # Require at least 50% of title words AND minimum 3 matches
                        # to prevent false positives on videos with shared words
                        # (e.g. all "BARLATES BODY BLITZ" videos matching each other)
                        min_required = max(3, len(title_words) // 2)
                        if best_match and best_score >= min_required:
                            potential_match = os.path.join(download_path, best_match)
                            self.log_message(f"Best match found: {best_match} (score: {best_score}/{len(title_words)} words)", "DEBUG")
                            downloaded_file = potential_match
                        elif best_match:
                            self.log_message(f"Fuzzy match rejected: {best_match} (score: {best_score}/{len(title_words)}, need {min_required})", "DEBUG")
                    
                except Exception as e:
                    self.log_message(f"Could not list download directory: {e}", "DEBUG")
            
            if not downloaded_file:
                return {
                    'success': False,
                    'error': f"Downloaded file not found. Expected in: {download_path}",
                    'actual_format': video_info['quality']
                }
            
            # Get file info and determine actual format
            file_size = os.path.getsize(downloaded_file)
            if file_size == 0:
                return {
                    'success': False,
                    'error': "Downloaded file is empty (0 bytes)",
                    'actual_format': video_info['quality']
                }
            
            # Determine actual format based on file extension and content
            actual_format = self.analyze_file_format(downloaded_file, video_info)
            
            self.log_message(f"File validation successful: {os.path.basename(downloaded_file)} ({file_size:,} bytes)", "DEBUG")
            
            return {
                'success': True,
                'actual_format': actual_format,
                'file_path': downloaded_file,
                'file_size': file_size
            }
            
        except Exception as e:
            return {
                'success': False,
                'error': f"File validation error: {str(e)}",
                'actual_format': video_info['quality']
            }

    def analyze_file_format(self, file_path, video_info):
        """Analyze the downloaded file to determine actual format/codec."""
        try:
            file_ext = os.path.splitext(file_path)[1].lower()
            
            if video_info['quality'].startswith('Audio-'):
                # For audio files, try to determine codec and bitrate
                return self.analyze_audio_format(file_path, file_ext)
            else:
                # For video files, try to determine resolution and codec
                return self.analyze_video_format(file_path, file_ext, video_info)
                
        except Exception as e:
            self.log_message(f"Format analysis failed: {e}", "DEBUG")
            # Fallback to basic format based on extension
            if video_info['quality'].startswith('Audio-'):
                return f"Audio {file_ext.upper()}"
            else:
                return f"Video {file_ext.upper()}"

    def analyze_audio_format(self, file_path, file_ext):
        """Analyze audio file to determine codec and bitrate."""
        try:
            # Try to use FFprobe if available for detailed analysis
            if self.check_ffmpeg_availability_status():
                result = subprocess.run([
                    'ffprobe', '-v', 'quiet', '-print_format', 'json', 
                    '-show_format', '-show_streams', file_path
                ], capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    import json
                    data = json.loads(result.stdout)
                    
                    for stream in data.get('streams', []):
                        if stream.get('codec_type') == 'audio':
                            codec = stream.get('codec_name', 'unknown')
                            bitrate = stream.get('bit_rate')
                            
                            if bitrate:
                                bitrate_kbps = int(bitrate) // 1000
                                return f"{bitrate_kbps}kbps {codec.upper()}"
                            else:
                                return f"{codec.upper()} Audio"
            
            # Fallback based on file extension
            ext_map = {
                '.mp3': 'MP3 Audio',
                '.m4a': 'AAC Audio', 
                '.aac': 'AAC Audio',
                '.webm': 'Opus Audio',
                '.ogg': 'Vorbis Audio',
                '.opus': 'Opus Audio'
            }
            
            return ext_map.get(file_ext, f"Audio {file_ext.upper()}")
            
        except Exception as e:
            self.log_message(f"Audio analysis failed: {e}", "DEBUG")
            return f"Audio {file_ext.upper()}"

    def analyze_video_format(self, file_path, file_ext, video_info):
        """Analyze video file to determine resolution and codec."""
        try:
            # Try to use FFprobe if available for detailed analysis
            if self.check_ffmpeg_availability_status():
                result = subprocess.run([
                    'ffprobe', '-v', 'quiet', '-print_format', 'json', 
                    '-show_format', '-show_streams', file_path
                ], capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    import json
                    data = json.loads(result.stdout)
                    
                    for stream in data.get('streams', []):
                        if stream.get('codec_type') == 'video':
                            width = stream.get('width')
                            height = stream.get('height')
                            codec = stream.get('codec_name', 'unknown')
                            
                            if height:
                                # Map original quality to actual downloaded quality
                                original_quality = video_info['quality']
                                if original_quality in ['Best', 'Lowest']:
                                    return f"{original_quality} → {height}p"
                                else:
                                    return f"{height}p"
                            else:
                                return f"{codec.upper()} Video"
            
            # Fallback - if we can't analyze, show what was requested vs adjusted
            if hasattr(video_info, 'adjusted_quality') and video_info.get('adjusted_quality'):
                return video_info['adjusted_quality']
            else:
                return video_info['quality']
                
        except Exception as e:
            self.log_message(f"Video analysis failed: {e}", "DEBUG")
            return video_info['quality']

    def validate_url(self, url):
        """Validate if the URL is a supported YouTube URL."""
        youtube_patterns = [
            r'(?:https?://)?(?:www\.)?youtube\.com/watch\?v=[\w-]+',
            r'(?:https?://)?(?:www\.)?youtube\.com/playlist\?list=[\w-]+',
            r'(?:https?://)?(?:www\.)?youtube\.com/channel/[\w-]+',
            r'(?:https?://)?(?:www\.)?youtube\.com/c/[\w-]+',
            r'(?:https?://)?(?:www\.)?youtube\.com/user/[\w-]+',
            r'(?:https?://)?(?:www\.)?youtube\.com/@[\w-]+',
            r'(?:https?://)?youtu\.be/[\w-]+',
            r'(?:https?://)?(?:www\.)?youtube\.com/shorts/[\w-]+'
        ]
        
        for pattern in youtube_patterns:
            if re.match(pattern, url, re.IGNORECASE):
                return True
        return False

    def add_url(self):
        """Handles adding a URL to the download queue."""
        url = self.url_entry.get().strip()
        if not url:
            messagebox.showwarning("Warning", "URL field cannot be empty.")
            return

        # Validate URL format
        if not self.validate_url(url):
            messagebox.showwarning("Warning", "Please enter a valid YouTube URL.\n\nSupported formats:\n• https://www.youtube.com/watch?v=VIDEO_ID\n• https://www.youtube.com/playlist?list=PLAYLIST_ID\n• https://youtu.be/VIDEO_ID\n• Channel URLs")
            return

        if self.audio_only_var.get():
            audio_format = self.audio_format_var.get()
            # Extract the format key from the display name
            format_key = audio_format.split()[0]  # Extract 'default', 'best', 'standard_mp3', etc.
            quality = f'Audio-{format_key}'
        else:
            quality = self.quality_var.get()
        self.url_entry.delete(0, tk.END)
        self.log_message(f"Processing URL: {url}")
        self.log_message("Processing URL... (This may take a moment for playlists)")
        threading.Thread(target=self._process_url_with_cache, args=(url, quality), daemon=True).start()

    def _process_url_with_cache(self, url, quality):
        """Process URL with caching to prevent multiple extractions."""
        cache_key = f"{url}_{quality}"
        
        # Check if cached and not expired
        if cache_key in self.info_cache:
            if self._is_cache_valid(cache_key):
                self.log_message(f"Using cached info for: {url}", "DEBUG")
                videos_to_add = self.info_cache[cache_key]
                if videos_to_add:
                    # Only log for significant batch sizes to reduce spam
                    if len(videos_to_add) > 5:
                        self.log_message(f"Adding {len(videos_to_add)} cached videos to GUI", "DEBUG")
                    self.root.after(0, self.add_videos_to_gui, videos_to_add)
                return
            else:
                # Remove expired cache
                del self.info_cache[cache_key]
                del self.cache_expiry[cache_key]
        
        # Prevent concurrent extraction of same URL
        if cache_key in self.extraction_locks:
            self.log_message(f"Extraction already in progress for: {url}", "DEBUG")
            return
        
        self.extraction_locks[cache_key] = True
        try:
            videos_to_add = self._extract_info(url, quality)
            if videos_to_add:  # Only cache successful results
                self.info_cache[cache_key] = videos_to_add
                self.cache_expiry[cache_key] = time.time() + 300  # 5 minute cache
                
                # Only log for significant batch sizes to reduce spam
                if len(videos_to_add) > 5:
                    self.log_message(f"Adding {len(videos_to_add)} videos to GUI", "DEBUG")
                self.root.after(0, self.add_videos_to_gui, videos_to_add)
        except Exception as e:
            self.log_message(f"Error in cached URL processing: {e}", "ERROR")
        finally:
            if cache_key in self.extraction_locks:
                del self.extraction_locks[cache_key]

    def _is_cache_valid(self, cache_key):
        """Check if cached data is still valid."""
        return (cache_key in self.cache_expiry and 
                time.time() < self.cache_expiry[cache_key])

    def cleanup_cache(self):
        """Clean up expired cache entries and limit memory usage."""
        current_time = time.time()
        expired_keys = [
            key for key, expiry_time in self.cache_expiry.items()
            if current_time > expiry_time
        ]
        
        for key in expired_keys:
            if key in self.info_cache:
                del self.info_cache[key]
            if key in self.cache_expiry:
                del self.cache_expiry[key]
        
        # Limit cache size (keep only most recent 1000 entries)
        if len(self.info_cache) > 1000:
            sorted_keys = sorted(
                self.cache_expiry.items(), 
                key=lambda x: x[1]
            )
            keys_to_remove = [key for key, _ in sorted_keys[:-1000]]
            
            for key in keys_to_remove:
                if key in self.info_cache:
                    del self.info_cache[key]
                if key in self.cache_expiry:
                    del self.cache_expiry[key]

    def periodic_cleanup(self):
        """Periodically clean up cache and resources."""
        self.cleanup_cache()
        self.root.after(300000, self.periodic_cleanup)  # Every 5 minutes

    def _extract_info(self, url, quality):
        """Extract info from URL (actual extraction logic)."""
        # This method contains the actual extraction logic from _process_url
        # but returns the result instead of updating GUI directly
        
        # Use unified options builder for extraction
        ydl_opts = self.build_ydl_opts(for_download=False)
        ydl_opts['extract_flat'] = 'in_playlist'  # Extract flat for playlists/channels
        
        try:
            self.log_message("Extracting video information...", "DEBUG")
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
            
            self.log_message("Extraction completed", "DEBUG")
            
            if not info:
                self.log_message("No information extracted from URL", "ERROR")
                return None
            
            videos_to_add = []
            
            if 'entries' in info:  # Playlist or channel
                all_entries = info['entries']
                valid_entries = [e for e in all_entries if e and e.get('id')]
                total_entries = len(valid_entries)
                
                self.log_message(f"Found {total_entries} videos in playlist/channel")
                
                # Use batch processing for large playlists (>20 items)
                if total_entries > 20:
                    self.log_message("Using batch processing for large playlist...")
                    videos_to_add = self._process_playlist_batch(valid_entries, quality)
                else:
                    # Keep sequential processing for small playlists to avoid overhead
                    for i, entry in enumerate(valid_entries):
                        video_url = f"https://www.youtube.com/watch?v={entry.get('id')}"
                        videos_to_add.append({
                            'title': entry.get('title', 'N/A'), 
                            'id': entry.get('id', 'N/A'), 
                            'url': video_url, 
                            'quality': quality,
                            'duration': self.format_duration(entry.get('duration'))
                        })
                        
                        # Update progress every 10 videos for small playlists
                        if (i + 1) % 10 == 0:
                            progress_msg = f"Processed {i + 1}/{total_entries} videos..."
                            self.log_message(progress_msg)
                
                self.log_message(f"Successfully processed all {len(videos_to_add)} videos from playlist/channel")
                
            else:  # Single video
                self.log_message("Processing single video", "DEBUG")
                # Use unified options builder for single video extraction
                ydl_opts_full = self.build_ydl_opts(for_download=False)
                ydl_opts_full['extract_flat'] = False  # Full extraction for single videos
                
                with yt_dlp.YoutubeDL(ydl_opts_full) as ydl_full:
                    full_info = ydl_full.extract_info(url, download=False)
                
                if full_info:
                    duration = self.format_duration(full_info.get('duration'))
                    
                    # Auto-adjust quality for single video
                    adjusted_quality = quality
                    if not quality.startswith('Audio-'):
                        adjusted_quality = self.check_and_adjust_single_video_quality(full_info, quality)
                    
                    videos_to_add.append({
                        'title': full_info.get('title', 'N/A'), 
                        'id': full_info.get('id', 'N/A'), 
                        'url': full_info.get('webpage_url', url), 
                        'quality': adjusted_quality,
                        'duration': duration,
                        'info': full_info  # Store complete info object
                    })
                    self.log_message(f"Added video: {full_info.get('title')}")
            
            return videos_to_add
            
        except Exception as e:
            error_str = str(e)
            if self._is_dpapi_error(error_str):
                self.log_message(
                    "Cookie extraction failed due to Chrome App-Bound Encryption (DPAPI). "
                    "Switch to 'From File' mode or use Firefox. "
                    "See: https://github.com/yt-dlp/yt-dlp/issues/10927",
                    "ERROR"
                )
                # Auto-disable broken cookie mode to prevent repeated failures
                self.root.after(0, lambda: self._handle_dpapi_failure())
            else:
                self.log_message(f"Error fetching video info: {e}", "ERROR")
            return None

    def _process_url(self, url, quality):
        """Worker function to fetch video info without blocking the GUI."""
        self.log_message(f"Starting to process URL: {url}", "DEBUG")
        
        # Use the extraction logic and handle GUI updates
        videos_to_add = self._extract_info(url, quality)
        
        # Use extract_flat for initial processing to avoid hanging
        # Use unified options builder for extraction
        ydl_opts = self.build_ydl_opts(for_download=False)
        ydl_opts['extract_flat'] = 'in_playlist'  # Extract flat for playlists/channels
        
        try:
            self.log_message("Extracting video information...", "DEBUG")
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
            
            self.log_message("Extraction completed", "DEBUG")
            
            if not info:
                self.log_message("No information extracted from URL", "ERROR")
                self.log_message("This could be due to:", "WARNING")
                self.log_message("• Invalid or private video URL", "INFO")
                self.log_message("• Network connectivity issues", "INFO")
                self.log_message("• YouTube server problems", "INFO")
                self.log_message("• Outdated yt-dlp version", "INFO")
                return
            
            videos_to_add = []
            
            if 'entries' in info: # Playlist or channel
                all_entries = info['entries']
                valid_entries = [e for e in all_entries if e and e.get('id')]
                total_entries = len(valid_entries)
                
                self.log_message(f"Found {total_entries} videos in playlist/channel")
                
                # Use batch processing for large playlists (>20 items)
                if total_entries > 20:
                    self.log_message("Using batch processing for large playlist... This will be faster!", "INFO")
                    videos_to_add = self._process_playlist_batch(valid_entries, quality)
                else:
                    # Keep sequential processing for small playlists to avoid overhead
                    self.log_message("Processing videos... This may take a while for large channels", "INFO")
                    
                    for i, entry in enumerate(valid_entries):
                        # For flat extraction, we get basic info
                        video_url = f"https://www.youtube.com/watch?v={entry.get('id')}"
                        videos_to_add.append({
                            'title': entry.get('title', 'N/A'), 
                            'id': entry.get('id', 'N/A'), 
                            'url': video_url, 
                            'quality': quality,
                            'duration': self.format_duration(entry.get('duration'))
                        })
                        
                        # Update progress every 10 videos for small playlists and show in console
                        if (i + 1) % 10 == 0:
                            progress_msg = f"Processed {i + 1}/{total_entries} videos..."
                            self.log_message(progress_msg)
                            # Also update GUI immediately for user feedback
                            self.root.after(0, lambda msg=progress_msg: self.log_message(msg, overwrite=True))
                
                self.log_message(f"Successfully processed all {len(videos_to_add)} videos from playlist/channel")
                
            else: # Single video - need full extraction
                self.log_message("Processing single video", "DEBUG")
                # For single videos, do a full extraction to get duration
                # Use unified options builder for single video extraction
                ydl_opts_full = self.build_ydl_opts(for_download=False)
                ydl_opts_full['extract_flat'] = False  # Full extraction for single videos
                
                with yt_dlp.YoutubeDL(ydl_opts_full) as ydl_full:
                    full_info = ydl_full.extract_info(url, download=False)
                
                if full_info:
                    duration = self.format_duration(full_info.get('duration'))
                    
                    # Auto-adjust quality for single video
                    adjusted_quality = quality
                    if not quality.startswith('Audio-'):
                        adjusted_quality = self.check_and_adjust_single_video_quality(full_info, quality)
                    
                    videos_to_add.append({
                        'title': full_info.get('title', 'N/A'), 
                        'id': full_info.get('id', 'N/A'), 
                        'url': full_info.get('webpage_url', url), 
                        'quality': adjusted_quality,
                        'duration': duration,
                        'info': full_info  # Store complete info object
                    })
                    self.log_message(f"Added video: {full_info.get('title')}")
            
            if videos_to_add:
                # For playlists, we'll check quality during download to avoid long processing times
                # For single videos, quality was already adjusted above
                if len(videos_to_add) == 1 and quality != 'Audio':
                    self.log_message("Quality check completed for single video", "DEBUG")
                elif len(videos_to_add) > 1:
                    self.log_message(f"Quality will be auto-adjusted during download for {len(videos_to_add)} videos", "INFO")
                
                # Only log for significant batch sizes to reduce spam
                if len(videos_to_add) > 5:
                    self.log_message(f"Adding {len(videos_to_add)} videos to GUI", "DEBUG")
                self.root.after(0, self.add_videos_to_gui, videos_to_add)
            else:
                self.log_message("No videos were extracted from the URL", "WARNING")
                
        except Exception as e:
            self.log_message(f"Error fetching video info: {e}", "ERROR")
            import traceback
            self.log_message(f"Traceback: {traceback.format_exc()}", "DEBUG")

    def _process_playlist_batch(self, entries, quality, batch_size=10):
        """Process playlist entries in batches for better performance."""
        videos_to_add = []
        
        # Process in batches
        for i in range(0, len(entries), batch_size):
            batch = entries[i:i + batch_size]
            batch_results = self._extract_batch_metadata(batch, quality)
            videos_to_add.extend(batch_results)
            
            # Update progress
            progress = min(i + batch_size, len(entries))
            self.log_message(f"Processed {progress}/{len(entries)} videos...")
            
        return videos_to_add

    def _extract_batch_metadata(self, entries, quality):
        """Extract metadata for a batch of entries concurrently."""
        results = []
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
            # Submit all tasks
            future_to_entry = {
                executor.submit(self._extract_single_entry, entry, quality): entry 
                for entry in entries
            }
            
            # Collect results as they complete
            for future in concurrent.futures.as_completed(future_to_entry):
                entry = future_to_entry[future]
                try:
                    result = future.result(timeout=30)
                    if result:
                        results.append(result)
                except Exception as e:
                    self.log_message(f"Failed to process {entry.get('id', 'unknown')}: {e}", "WARNING")
        
        return results

    def _extract_single_entry(self, entry, quality):
        """Extract metadata for a single entry with rate limiting."""
        with self.extraction_semaphore:
            try:
                # Add small delay to avoid rate limiting
                time.sleep(0.1)
                
                video_url = f"https://www.youtube.com/watch?v={entry.get('id')}"
                return {
                    'title': entry.get('title', 'N/A'),
                    'id': entry.get('id', 'N/A'),
                    'url': video_url,
                    'quality': quality,
                    'duration': self.format_duration(entry.get('duration'))
                }
            except Exception as e:
                self.log_message(f"Error processing entry: {e}", "DEBUG")
                return None

    def auto_adjust_quality(self, videos_to_add, requested_quality):
        """Auto-adjust video quality based on available formats."""
        quality_hierarchy = ['Best', '1080p', '720p', '480p', '360p']
        adjusted_videos = []
        
        for video in videos_to_add:
            if video['quality'].startswith('Audio-'):
                adjusted_videos.append(video)
                continue
            
            # If "Best" is requested, no adjustment needed
            if video['quality'] == 'Best':
                adjusted_videos.append(video)
                continue
                
            try:
                # Get available formats for this video
                ydl_opts = {
                    'skip_download': True,
                    'listformats': False,
                    # Use non-web client(s) to avoid SABR-only responses
                    'extractor_args': {
                        'youtube': {
                            'player_client': ['android', 'ios', 'tv']
                        }
                    }
                }
                
                # Configure logger and quiet settings
                ydl_opts = self.configure_ydl_opts_with_logger(ydl_opts)
                
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info = ydl.extract_info(video['url'], download=False)
                    
                if info and 'formats' in info:
                    available_heights = set()
                    
                    # Extract available video heights
                    for fmt in info['formats']:
                        if fmt.get('vcodec') != 'none' and fmt.get('height'):
                            available_heights.add(fmt['height'])
                    
                    # Convert to quality strings
                    available_qualities = []
                    max_height = max(available_heights) if available_heights else 0
                    
                    # Add "Best" if there are high-resolution formats available
                    if max_height >= 1440:  # 1440p or higher
                        available_qualities.append('Best')
                    
                    for height in available_heights:
                        if height >= 1080:
                            available_qualities.append('1080p')
                        elif height >= 720:
                            available_qualities.append('720p')
                        elif height >= 480:
                            available_qualities.append('480p')
                        elif height >= 360:
                            available_qualities.append('360p')
                    
                    # Remove duplicates and sort by quality hierarchy
                    available_qualities = list(set(available_qualities))
                    available_qualities.sort(key=lambda x: quality_hierarchy.index(x) if x in quality_hierarchy else 999)
                    
                    # Find the best available quality that's <= requested quality
                    requested_index = quality_hierarchy.index(requested_quality) if requested_quality in quality_hierarchy else 0
                    best_quality = requested_quality
                    
                    for quality in quality_hierarchy[requested_index:]:
                        if quality in available_qualities:
                            best_quality = quality
                            break
                    
                    # If requested quality is not available, use the highest available
                    if requested_quality not in available_qualities and available_qualities:
                        best_quality = available_qualities[0]  # Highest available
                        self.log_message(f"Quality adjusted for '{video['title'][:50]}...': {requested_quality} → {best_quality}", "INFO")
                    
                    video['quality'] = best_quality
                else:
                    # If we can't get format info, keep original quality
                    # Reduce logging verbosity for format checks
                    pass  # Keep original quality silently
                    
            except Exception as e:
                # If quality check fails, keep original quality
                # Only log quality check failures for non-network errors
                if "network" not in str(e).lower() and "timeout" not in str(e).lower():
                    self.log_message(f"Quality check failed for '{video['title'][:50]}...': {e}", "DEBUG")
                
            adjusted_videos.append(video)
        
        return adjusted_videos

    def check_and_adjust_single_video_quality(self, video_info, requested_quality):
        """Check and adjust quality for a single video based on available formats."""
        if not video_info.get('formats'):
            return requested_quality
        
        # If "Best" is requested, return it as-is (no adjustment needed)
        if requested_quality == 'Best':
            return requested_quality
            
        quality_hierarchy = ['Best', '1080p', '720p', '480p', '360p']
        quality_to_height = {'1080p': 1080, '720p': 720, '480p': 480, '360p': 360}
        requested_height = quality_to_height.get(requested_quality, 1080)
        
        available_heights = set()
        has_audio = False
        
        # First, check what video heights are available and if there's audio
        for fmt in video_info['formats']:
            # Check for video formats (including video-only)
            if fmt.get('vcodec') != 'none' and fmt.get('height'):
                available_heights.add(fmt['height'])
            
            # Check if there's any audio available
            if fmt.get('acodec') != 'none':
                has_audio = True
        
        if not available_heights:
            self.log_message(f"No video formats found for '{video_info.get('title', 'Unknown')[:50]}...', keeping {requested_quality}", "DEBUG")
            return requested_quality
        
        if not has_audio:
            self.log_message(f"No audio formats found for '{video_info.get('title', 'Unknown')[:50]}...', but proceeding with video-only", "DEBUG")
        
        # Find the best available height that matches or is closest to requested
        # First try to find exact match or higher
        suitable_heights = [h for h in available_heights if h >= requested_height]
        
        if suitable_heights:
            # Use the lowest height that's >= requested (closest match)
            best_height = min(suitable_heights)
        else:
            # If no height >= requested, use the highest available
            best_height = max(available_heights)
        
        # Convert back to quality string
        if best_height >= 2160:
            best_quality = 'Best'  # 4K or higher, use Best
        elif best_height >= 1440:
            best_quality = 'Best'  # 1440p, use Best
        elif best_height >= 1080:
            best_quality = '1080p'
        elif best_height >= 720:
            best_quality = '720p'
        elif best_height >= 480:
            best_quality = '480p'
        else:
            best_quality = '360p'
        
        # Only log adjustment if it actually changed and it's a significant change
        if best_quality != requested_quality:
            self.log_message(f"Quality auto-adjusted: '{video_info.get('title', 'Unknown')[:50]}...' {requested_quality} → {best_quality} (available: {sorted(available_heights, reverse=True)})", "INFO")
            # Store the adjusted quality for later GUI update
            video_info['adjusted_quality'] = best_quality
        
        return best_quality

    def check_quality_before_download(self, video_info):
        """Check and adjust quality just before download."""
        # Skip quality check for audio formats
        if video_info['quality'].startswith('Audio-'):
            return video_info['quality']
            
        try:
            # Use unified options builder for quality checking
            ydl_opts = self.build_ydl_opts(for_download=False)
            
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(video_info['url'], download=False)
                
            if info:
                return self.check_and_adjust_single_video_quality(info, video_info['quality'])
        except Exception as e:
            self.log_message(f"Could not check quality for {video_info['title']}: {e}", "DEBUG")
        
        return video_info['quality']

    def update_video_quality_in_gui(self, item_id, new_quality):
        """Update the quality display in the GUI."""
        if not self.tree.exists(item_id):
            return
            
        current_values = list(self.tree.item(item_id, 'values'))
        if len(current_values) >= 3:
            current_values[2] = new_quality  # Quality is back to index 2
            self.tree.item(item_id, values=current_values)

    def format_duration(self, duration_seconds):
        """Format duration from seconds to HH:MM:SS or MM:SS format."""
        if duration_seconds is None:
            return 'N/A'
        
        try:
            duration_seconds = int(duration_seconds)
            hours = duration_seconds // 3600
            minutes = (duration_seconds % 3600) // 60
            seconds = duration_seconds % 60
            
            if hours > 0:
                return f"{hours:02d}:{minutes:02d}:{seconds:02d}"
            else:
                return f"{minutes:02d}:{seconds:02d}"
        except (ValueError, TypeError):
            return 'N/A'

    def add_videos_to_gui(self, videos):
        """Adds video information to the Treeview and internal queue."""
        # Check for duplicates
        existing_ids = {video.get('id') for video in self.download_queue}
        new_videos = []
        duplicate_count = 0
        
        for video in videos:
            if video.get('id') not in existing_ids:
                new_videos.append(video)
                existing_ids.add(video.get('id'))  # Add to set to prevent duplicates within this batch
            else:
                duplicate_count += 1
        
        if duplicate_count > 0:
            self.log_message(f"Skipped {duplicate_count} duplicate video(s) that were already in the queue", "INFO")
        
        if new_videos:
            self.log_message(f"Adding {len(new_videos)} new video(s) to queue", "INFO")
            self._insert_videos_chunked(list(new_videos))
            
            # Trigger SABR detection if not in SABR mode and haven't checked recently
            should_check_sabr = (
                not self.sabr_mode_active and 
                (self.last_sabr_check is None or 
                 (time.time() - self.last_sabr_check) > 3600)  # Check every hour
            )
            
            if should_check_sabr:
                self.log_message("Triggering SABR detection for new URL...", "DEBUG")
                self.trigger_sabr_detection(new_videos[0].get('url', ''))
        else:
            self.log_message("No new videos to add - all videos were already in the queue", "INFO")

    def remove_selected(self):
        """Removes the selected video from the queue."""
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "No video selected to remove.")
            return

        for item_id in selected_items:
            self.download_queue = [v for v in self.download_queue if v['item_id'] != item_id]
            self.tree.delete(item_id)
        self.log_message(f"Removed {len(selected_items)} item(s) from the queue.")
        self.update_reset_button_state()  # Update reset button after removal
        self.update_status_summary()  # Update status summary after removal
        self.update_line_numbers()  # Update line numbers after removal
        self.schedule_save_settings()

    def clear_all(self):
        """Clears all items from the download queue."""
        if not self.download_queue:
            messagebox.showinfo("Info", "Download queue is already empty.")
            return
            
        if messagebox.askyesno("Confirm", "Are you sure you want to clear all items from the queue?"):
            # Clear the treeview
            for item in self.tree.get_children():
                self.tree.delete(item)
            
            # Clear the internal queue
            self.download_queue.clear()
            self.log_message("Cleared all items from the queue.")
            self.update_reset_button_state()  # Update reset button after clearing
            self.update_status_summary()  # Update status summary after clearing
            self.update_line_numbers()  # Update line numbers after clearing
            self.schedule_save_settings()

    def move_up(self):
        """Moves selected items up in the queue."""
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "No video selected to move.")
            return

        # Get all items and their positions
        all_items = self.tree.get_children()
        
        # Check if any selected item is already at the top
        if selected_items[0] == all_items[0]:
            return  # Can't move up further
        
        # Move each selected item up
        moved_items = []
        for item_id in selected_items:
            current_index = all_items.index(item_id)
            if current_index > 0:
                # Move in treeview
                self.tree.move(item_id, '', current_index - 1)
                
                # Move in internal queue
                video_to_move = None
                for i, video in enumerate(self.download_queue):
                    if video['item_id'] == item_id:
                        video_to_move = self.download_queue.pop(i)
                        self.download_queue.insert(max(0, i - 1), video_to_move)
                        break
                
                moved_items.append(item_id)
        
        # Restore selection
        self.tree.selection_set(moved_items)
        self.log_message(f"Moved {len(moved_items)} item(s) up in the queue.")
        self.update_line_numbers()  # Update line numbers after moving
        self.schedule_save_settings()

    def move_down(self):
        """Moves selected items down in the queue."""
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "No video selected to move.")
            return

        # Get all items and their positions
        all_items = self.tree.get_children()
        
        # Check if any selected item is already at the bottom
        if selected_items[-1] == all_items[-1]:
            return  # Can't move down further
        
        # Move each selected item down (process in reverse order)
        moved_items = []
        for item_id in reversed(selected_items):
            current_index = all_items.index(item_id)
            if current_index < len(all_items) - 1:
                # Move in treeview
                self.tree.move(item_id, '', current_index + 1)
                
                # Move in internal queue
                video_to_move = None
                for i, video in enumerate(self.download_queue):
                    if video['item_id'] == item_id:
                        video_to_move = self.download_queue.pop(i)
                        self.download_queue.insert(min(len(self.download_queue), i + 1), video_to_move)
                        break
                
                moved_items.append(item_id)
        
        # Restore selection
        self.tree.selection_set(moved_items)
        self.log_message(f"Moved {len(moved_items)} item(s) down in the queue.")
        self.update_line_numbers()  # Update line numbers after moving
        self.schedule_save_settings()

    def move_to_top(self):
        """Moves selected items to the top of the queue."""
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "No video selected to move.")
            return

        # Get all items and their positions
        all_items = self.tree.get_children()
        
        # Check if the first selected item is already at the top
        if selected_items[0] == all_items[0]:
            return  # Already at the top
        
        # Move each selected item to the top (process in reverse order to maintain relative order)
        moved_items = []
        videos_to_move = []
        
        # First, collect all videos to move and remove them from the queue
        for item_id in reversed(selected_items):
            for i, video in enumerate(self.download_queue):
                if video['item_id'] == item_id:
                    video_to_move = self.download_queue.pop(i)
                    videos_to_move.append(video_to_move)
                    break
        
        # Insert all videos at the beginning of the queue (reverse order to maintain selection order)
        for video in reversed(videos_to_move):
            self.download_queue.insert(0, video)
        
        # Move items in treeview to the top
        for i, item_id in enumerate(selected_items):
            self.tree.move(item_id, '', i)
            moved_items.append(item_id)
        
        # Restore selection
        self.tree.selection_set(moved_items)
        self.log_message(f"Moved {len(moved_items)} item(s) to the top of the queue.")
        self.update_line_numbers()  # Update line numbers after moving
        self.schedule_save_settings()

    def move_to_bottom(self):
        """Moves selected items to the bottom of the queue."""
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "No video selected to move.")
            return

        # Get all items and their positions
        all_items = self.tree.get_children()
        
        # Check if the last selected item is already at the bottom
        if selected_items[-1] == all_items[-1]:
            return  # Already at the bottom
        
        # Move each selected item to the bottom (maintain relative order)
        moved_items = []
        videos_to_move = []
        
        # First, collect all videos to move and remove them from the queue
        for item_id in selected_items:
            for i, video in enumerate(self.download_queue):
                if video['item_id'] == item_id:
                    video_to_move = self.download_queue.pop(i)
                    videos_to_move.append(video_to_move)
                    break
        
        # Append all videos to the end of the queue (maintain selection order)
        for video in videos_to_move:
            self.download_queue.append(video)
        
        # Move items in treeview to the bottom
        total_items = len(all_items)
        for i, item_id in enumerate(selected_items):
            # Move to the end, accounting for items already moved
            target_position = total_items - len(selected_items) + i
            self.tree.move(item_id, '', target_position)
            moved_items.append(item_id)
        
        # Restore selection
        self.tree.selection_set(moved_items)
        self.log_message(f"Moved {len(moved_items)} item(s) to the bottom of the queue.")
        self.update_line_numbers()  # Update line numbers after moving
        self.schedule_save_settings()

    def sort_treeview(self, column):
        """Sorts the treeview by the specified column."""
        # Determine sort order
        if self.sort_column == column:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_column = column
            self.sort_reverse = False

        # Update column headings to show sort indicators
        self.update_column_headings()

        # Get all items with their values
        items = []
        for item_id in self.tree.get_children():
            values = self.tree.item(item_id, 'values')
            items.append((item_id, values))

        # Sort items based on the selected column
        column_index = {'Name': 0, 'ID': 1, 'Quality': 2, 'Duration': 3, 'Status': 4}[column]
        
        if column == 'Duration':
            # Special sorting for duration (convert to seconds for comparison)
            items.sort(key=lambda x: self.duration_to_seconds(x[1][column_index]), reverse=self.sort_reverse)
        else:
            # Regular string sorting
            items.sort(key=lambda x: x[1][column_index].lower(), reverse=self.sort_reverse)

        # Reorder items in treeview
        for index, (item_id, values) in enumerate(items):
            self.tree.move(item_id, '', index)

        # Reorder internal queue to match
        new_queue = []
        for item_id, values in items:
            for video in self.download_queue:
                if video['item_id'] == item_id:
                    new_queue.append(video)
                    break
        
        self.download_queue = new_queue
        self.log_message(f"Sorted by {column} ({'descending' if self.sort_reverse else 'ascending'})")
        self.schedule_save_settings()

    def update_column_headings(self):
        """Updates column headings to show sort indicators."""
        columns = {'Name': 'Video Title', 'ID': 'Video ID', 'Quality': 'Format', 'Duration': 'Duration', 'Status': 'Status'}
        
        for col, title in columns.items():
            if col == self.sort_column:
                indicator = ' ↓' if self.sort_reverse else ' ↑'
                self.tree.heading(col, text=title + indicator)
            else:
                self.tree.heading(col, text=title)

    def duration_to_seconds(self, duration_str):
        """Converts duration string to seconds for sorting."""
        if duration_str == 'N/A':
            return 0
        
        try:
            parts = duration_str.split(':')
            if len(parts) == 2:  # MM:SS
                return int(parts[0]) * 60 + int(parts[1])
            elif len(parts) == 3:  # HH:MM:SS
                return int(parts[0]) * 3600 + int(parts[1]) * 60 + int(parts[2])
            else:
                return 0
        except (ValueError, IndexError):
            return 0

    def start_download(self):
        """Starts the download process."""
        if not self.download_queue:
            messagebox.showinfo("Info", "Download queue is empty.")
            return
        
        # Check if there are any pending videos to download
        pending_videos = [v for v in self.download_queue if v.get('status', 'Pending') == 'Pending']
        if not pending_videos:
            messagebox.showinfo("Info", "No pending videos to download. All videos are either completed, failed, or skipped.")
            return
            
        if self.is_downloading:
            messagebox.showwarning("Warning", "A download is already in progress.")
            return
        
        # Trigger SABR detection if not in SABR mode and haven't checked recently
        should_check_sabr = (
            not self.sabr_mode_active and 
            (self.last_sabr_check is None or 
             (time.time() - self.last_sabr_check) > 3600) and  # Check every hour
            pending_videos
        )
        
        if should_check_sabr:
            test_url = pending_videos[0].get('url', '')
            if test_url:
                self.log_message("Triggering SABR detection before download start...", "DEBUG")
                self.trigger_sabr_detection(test_url)
        
        self.is_downloading = True
        self.stop_event.clear()
        self.update_button_states()

        self.download_thread = threading.Thread(target=self.download_worker, daemon=True)
        self.download_thread.start()
        self.log_message(f"--- Download process started for {len(pending_videos)} pending video(s) ---")

    def stop_download(self):
        """Signals the download thread to stop."""
        if self.is_downloading:
            self._stop_start_time = time.time()
            self._current_download_cancelled = True
            self.log_message("STOP: User clicked stop button", "WARNING")
            self.stop_event.set()
            self.log_message("STOP: Stop event flag set", "WARNING")
            self.log_message("--- Stop signal sent. Stopping after current file... ---", "WARNING")
            self.log_message("Note: Current download will be reset to pending status.", "INFO")
            
            # Update button states immediately to show stop is in progress
            self.stop_button.config(text="⏸", state=tk.DISABLED)  # Pause icon to indicate stopping
            self.log_message("STOP: Stop button disabled", "WARNING")
            
            # If there's an active yt-dlp process, we can't force stop it
            # but we can prevent new downloads from starting
            if self.ydl_process:
                self.log_message("STOP: Active yt-dlp process detected, waiting for cancellation...", "WARNING")
            else:
                self.log_message("STOP: No active yt-dlp process", "WARNING")

    def download_worker(self):
        """The main worker function that downloads videos one by one."""
        download_path = self.download_path.get()
        if not os.path.isdir(download_path):
             self.log_message(f"Error: Download path '{download_path}' does not exist. Please select a valid folder.", "ERROR")
             self.is_downloading = False
             self.root.after(0, self.update_button_states)
             return

        current_index = 0
        current_downloading_video = None  # Track currently downloading video
        
        while current_index < len(self.download_queue) and not self.stop_event.is_set():
            video_info = self.download_queue[current_index]
            self.ydl_process = None
            
            # Skip videos that are already completed, failed, or skipped
            if video_info.get('status') in ['Done', 'Failed', 'Skipped']:
                self.log_message(f"Skipping {video_info.get('status', 'completed').lower()} video: {video_info['title']}")
                current_index += 1
                continue
            
            # File existence check is now handled by yt-dlp's download archive
            
            try:
                # Set status to downloading and track this video
                current_downloading_video = video_info
                self.root.after(0, self.update_video_status, video_info['item_id'], 'Downloading')
                self.log_message(f"Starting download: {video_info['title']}")
                
                # Auto-adjust quality if needed (for videos that weren't checked during URL processing)
                if not video_info['quality'].startswith('Audio-') and 'info' not in video_info:
                    original_quality = video_info['quality']
                    adjusted_quality = self.check_quality_before_download(video_info)
                    if adjusted_quality != original_quality:
                        video_info['quality'] = adjusted_quality
                        # Update the GUI to show the adjusted quality
                        self.root.after(0, self.update_video_quality_in_gui, video_info['item_id'], adjusted_quality)
                
                self.last_progress_time = 0  # Reset progress timer for new download
                self.stop_message_logged = False  # Reset stop message flag for new download
                
                # Setup yt-dlp options using unified builder
                ydl_opts = self.build_ydl_opts(video_info, download_path, for_download=True)
                
                # Log the yt-dlp configuration for debugging
                # Log configuration only once per session to reduce spam
                if not hasattr(self, '_config_logged'):
                    self.log_message(f"yt-dlp configuration: format='{ydl_opts.get('format', 'default')}', retries={ydl_opts.get('retries', 0)}", "DEBUG")
                    ea = ydl_opts.get('extractor_args', {}).get('youtube', {})
                    clients = ea.get('player_client', ['default'])
                    self.log_message(f"Player clients: {', '.join(clients)}, JS runtime: node", "DEBUG")
                    self._config_logged = True
                
                # Clear any previous cancellation flags
                self._current_download_cancelled = False
                
                # Create a cancellation monitor for this download
                download_cancelled = threading.Event()
                
                def cancellation_monitor():
                    """Monitor for stop requests and interrupt yt-dlp if needed"""
                    start_time = time.time()
                    while not download_cancelled.is_set():
                        if self.stop_event.is_set():
                            elapsed = time.time() - start_time
                            self.log_message(f"MONITOR: Stop detected after {elapsed:.1f}s, forcing cancellation", "WARNING")
                            
                            # Try to interrupt more aggressively
                            if hasattr(self, 'ydl_process') and self.ydl_process:
                                try:
                                    # Try to interrupt the yt-dlp process more directly
                                    self.log_message("MONITOR: Attempting to interrupt yt-dlp process", "WARNING")
                                    # Set a flag that our custom logger will check
                                    download_cancelled.set()
                                except Exception as e:
                                    self.log_message(f"MONITOR: Error interrupting process: {e}", "WARNING")
                            
                            download_cancelled.set()
                            return
                        time.sleep(0.05)  # Check every 50ms for faster response
                
                # Start the cancellation monitor
                monitor_thread = threading.Thread(target=cancellation_monitor, daemon=True)
                monitor_thread.start()
                
                # Create a timeout mechanism for the entire yt-dlp operation
                download_result = {'success': False, 'error': None}
                
                def run_ytdlp():
                    """Run yt-dlp in a separate thread so we can timeout/cancel it"""
                    try:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            # Store reference for potential termination
                            self.ydl_process = ydl
                            
                            # Check for stop before starting download
                            if self.stop_event.is_set() or download_cancelled.is_set():
                                self.log_message("STOP: Download stopped before starting this video.", "WARNING")
                                download_result['error'] = 'cancelled_before_start'
                                return
                            
                            # Always do a fresh extraction+download to get fresh URLs.
                            # Cached info from earlier extraction contains m3u8/HLS URLs
                            # with time-limited auth tokens that expire within seconds.
                            # Using stale URLs → 403 Forbidden on HLS fragments.
                            if self.stop_event.is_set() or download_cancelled.is_set():
                                self.log_message("STOP: Cancelled before starting download", "WARNING")
                                raise yt_dlp.utils.DownloadCancelled('User requested stop')
                            ydl.download([video_info['url']])
                        
                        download_result['success'] = True
                    except Exception as e:
                        download_result['error'] = e
                
                # Start yt-dlp in a separate thread
                ytdlp_thread = threading.Thread(target=run_ytdlp, daemon=True)
                ytdlp_thread.start()
                
                # Wait for completion or cancellation with timeout
                # Check the result and handle errors within try block
                try:
                    start_time = time.time()
                    while ytdlp_thread.is_alive():
                        if self.stop_event.is_set() or download_cancelled.is_set():
                            elapsed = time.time() - start_time
                            self.log_message(f"TIMEOUT: Forcing termination after {elapsed:.1f}s", "WARNING")
                            # Give yt-dlp a moment to respond to cancellation
                            ytdlp_thread.join(timeout=1.0)
                            if ytdlp_thread.is_alive():
                                self.log_message("TIMEOUT: yt-dlp thread still alive, raising cancellation", "WARNING")
                                raise yt_dlp.utils.DownloadCancelled('Forced timeout cancellation')
                            break
                        time.sleep(0.1)
                    if download_result.get('error'):
                        if download_result['error'] == 'cancelled_before_start':
                            # Reset status back to pending since we didn't actually start
                            self.root.after(0, self.update_video_status, video_info['item_id'], 'Pending')
                            current_downloading_video = None
                            break
                        else:
                            # Re-raise the error to be caught by specific exception handlers
                            raise download_result['error']
                    
                    # If no error, wait for thread to complete
                    ytdlp_thread.join(timeout=0.1)
                
                except yt_dlp.utils.DownloadCancelled:
                    # Handle user-requested cancellation
                    self.log_message('CANCEL: DownloadCancelled exception caught', 'WARNING')
                    self.log_message('CANCEL: Resetting video status to Pending', 'WARNING')
                    self.root.after(0, self.update_video_status, video_info['item_id'], 'Pending')
                    current_downloading_video = None
                    self.log_message('CANCEL: Breaking out of download loop', 'WARNING')
                    break
                except yt_dlp.DownloadError as e:
                    # Handle yt-dlp specific download errors
                    error_msg = str(e)
                    if self._is_dpapi_error(error_msg):
                        self.log_message(
                            "Cookie extraction failed (DPAPI / App-Bound Encryption). "
                            "Switch cookies to 'From File' mode or use Firefox. "
                            "See: https://github.com/yt-dlp/yt-dlp/issues/10927",
                            "ERROR"
                        )
                        self.root.after(0, lambda: self._handle_dpapi_failure())
                        raise Exception("Cookie decryption blocked by Chrome — switch to 'From File' mode")
                    self.log_message(f"yt-dlp DownloadError: {error_msg}", "ERROR")
                    raise Exception(f"Download failed: {error_msg}")
                except yt_dlp.utils.ExtractorError as e:
                    # Handle extraction errors
                    error_msg = str(e)
                    self.log_message(f"yt-dlp ExtractorError: {error_msg}", "ERROR")
                    raise Exception(f"Video extraction failed: {error_msg}")
                except Exception as e:
                    # Handle any other yt-dlp related errors
                    error_msg = str(e)
                    self.log_message(f"yt-dlp error: {error_msg}", "ERROR")
                    raise
                finally:
                    # Always signal the monitor to stop
                    download_cancelled.set()

                # Check if stop was requested after download completion
                if self.stop_event.is_set():
                    self.log_message("Download stopped by user after completing current video.", "WARNING")
                    # Reset the video back to pending since user wants to stop
                    self.root.after(0, self.update_video_status, video_info['item_id'], 'Pending')
                    current_downloading_video = None
                    break
                
                # Validate downloaded file and update format info
                validation_result = self.validate_downloaded_file(video_info)
                
                if validation_result['success']:
                    # Set status to done and update format column with actual downloaded info
                    self.root.after(0, self.update_video_status, video_info['item_id'], 'Done')
                    self.root.after(0, self.update_video_quality_in_gui, video_info['item_id'], validation_result['actual_format'])
                    
                    # Enhanced completion logging with progress context
                    remaining = len([v for v in self.download_queue[current_index+1:] if v.get('status', 'Pending') == 'Pending'])
                    if remaining > 0:
                        self.log_message(f"Successfully downloaded: {video_info['title']} ({remaining} remaining)", "INFO")
                    else:
                        self.log_message(f"Successfully downloaded: {video_info['title']}", "INFO")
                else:
                    # File validation failed - mark as failed
                    self.root.after(0, self.update_video_status, video_info['item_id'], 'Failed')
                    self.log_message(f"Download validation failed for '{video_info['title']}': {validation_result['error']}", "ERROR")
                current_downloading_video = None
                current_index += 1
                
            except Exception as e:
                if self.stop_event.is_set():
                    self.log_message(f"EXCEPTION: Download stopped by user during exception: {type(e).__name__}", "WARNING")
                    # Reset the currently downloading video back to pending
                    if current_downloading_video:
                        self.log_message("EXCEPTION: Resetting interrupted video to Pending", "WARNING")
                        self.root.after(0, self.update_video_status, current_downloading_video['item_id'], 'Pending')
                        current_downloading_video = None
                    self.log_message("EXCEPTION: Breaking out of download loop", "WARNING")
                    break
                
                # Classify the error and set appropriate status
                error_str = str(e)
                status = self.classify_download_error(error_str, video_info)
                
                self.root.after(0, self.update_video_status, video_info['item_id'], status)
                self.log_message(f"Error downloading {video_info['title']}: {e}", "ERROR")
                
                # Provide troubleshooting suggestions for common errors
                self.suggest_troubleshooting(error_str)
                current_downloading_video = None
                current_index += 1
                continue
            finally:
                self.ydl_process = None
        
        # If we exited the loop due to stop event and there's still a downloading video, reset it
        if self.stop_event.is_set() and current_downloading_video:
            self.root.after(0, self.update_video_status, current_downloading_video['item_id'], 'Pending')
            self.log_message(f"Reset status to pending for interrupted download: {current_downloading_video['title']}", "INFO")

        # Check if we stopped due to user request
        was_stopped = self.stop_event.is_set()
        
        if was_stopped:
            self.log_message("WORKER: Download worker exiting due to stop request", "WARNING")
        else:
            self.log_message("WORKER: Download worker exiting normally", "INFO")
        
        self.is_downloading = False
        self.stop_event.clear()
        self.log_message("WORKER: Download flags cleared", "WARNING" if was_stopped else "INFO")
        
        # Count remaining pending videos
        remaining_pending = sum(1 for v in self.download_queue if v.get('status', 'Pending') == 'Pending')
        
        if was_stopped:
            self.log_message(f"--- Download process stopped. {remaining_pending} videos remain pending ---", "WARNING")
        else:
            self.log_message("--- Download process finished ---")
            if remaining_pending > 0:
                self.log_message(f"Note: {remaining_pending} videos remain pending (may have been skipped or failed)", "INFO")
        
        self.root.after(0, self.update_button_states)
        self.root.after(0, self.update_status_summary)



    def update_video_status(self, item_id, status):
        """Updates the status of a video in the treeview with appropriate colors."""
        if not self.tree.exists(item_id):
            return
            
        # Update internal data
        for video in self.download_queue:
            if video['item_id'] == item_id:
                video['status'] = status
                break
        
        # Update GUI with status text and colors
        current_values = list(self.tree.item(item_id, 'values'))
        if len(current_values) >= 5:
            # Set status display text and color tag (Status is back to index 4)
            if status == 'Pending':
                current_values[4] = 'Pending'
                self.tree.item(item_id, values=current_values, tags=('pending',))
            elif status == 'Downloading':
                current_values[4] = '↓ Downloading'
                self.tree.item(item_id, values=current_values, tags=('downloading',))
            elif status == 'Done':
                current_values[4] = 'Done'
                self.tree.item(item_id, values=current_values, tags=('done',))
            elif status == 'Failed':
                current_values[4] = 'Failed'
                self.tree.item(item_id, values=current_values, tags=('failed',))
            elif status == 'Skipped':
                current_values[4] = 'Skipped'
                self.tree.item(item_id, values=current_values, tags=('skipped',))
            elif status == 'QualityBlocked':
                current_values[4] = 'QualityBlocked'
                self.tree.item(item_id, values=current_values, tags=('qualityblocked',))
            elif status == 'AgeRestricted':
                current_values[4] = 'AgeRestricted'
                self.tree.item(item_id, values=current_values, tags=('agerestricted',))
        
        # Update reset button state and status summary
        self.update_reset_button_state()
        self.update_status_summary()
        self.update_line_numbers()  # Update line numbers when status changes



    def reset_selected(self):
        """Reset selected videos by deleting files and setting status to Pending."""
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("Warning", "No videos selected to reset.")
            return
        
        # Check if any selected items can be reset
        resetable_items = []
        for item_id in selected_items:
            current_values = self.tree.item(item_id, 'values')
            if len(current_values) >= 5:
                status = current_values[4]  # Status is back to index 4
                if status in ['Done', 'Failed', 'Skipped', 'QualityBlocked', 'AgeRestricted']:
                    resetable_items.append(item_id)
        
        if not resetable_items:
            messagebox.showinfo("Info", "No resetable videos selected. Only Done, Failed, Skipped, QualityBlocked, or AgeRestricted videos can be reset.")
            return
        
        if messagebox.askyesno("Confirm Reset", f"Are you sure you want to reset {len(resetable_items)} video(s)? This will delete existing files and restart the download."):
            # Disable reset button during operation
            self.reset_button.config(state=tk.DISABLED)
            self.log_message(f"Resetting {len(resetable_items)} video(s)...")
            
            # Start background worker
            threading.Thread(target=self._reset_worker, args=(resetable_items,), daemon=True).start()

    def _reset_worker(self, item_ids):
        """Background worker to reset videos without blocking UI."""
        try:
            download_path = self.download_path.get()
            archive_path = os.path.join(download_path, 'download-archive.txt')
            
            # Load archive once into memory for efficient processing
            archive_lines = []
            if os.path.exists(archive_path):
                try:
                    with open(archive_path, 'r', encoding='utf-8') as f:
                        archive_lines = f.readlines()
                except Exception as e:
                    self.root.after(0, lambda: self.log_message(f"Error reading archive: {e}", "WARNING"))
            
            # Collect video IDs to remove from archive
            video_ids_to_remove = set()
            videos_to_reset = []
            
            for item_id in item_ids:
                # Find video info
                video_info = None
                for video in self.download_queue:
                    if video['item_id'] == item_id:
                        video_info = video
                        break
                
                if video_info and video_info.get('id'):
                    video_ids_to_remove.add(video_info['id'])
                    videos_to_reset.append((item_id, video_info))
            
            # Remove all selected IDs from archive in one pass
            if video_ids_to_remove and archive_lines:
                new_lines = []
                removed_count = 0
                for line in archive_lines:
                    line_stripped = line.strip()
                    should_remove = False
                    for video_id in video_ids_to_remove:
                        if line_stripped.endswith(video_id):
                            should_remove = True
                            removed_count += 1
                            break
                    if not should_remove:
                        new_lines.append(line)
                
                # Write archive once if changes were made
                if removed_count > 0:
                    try:
                        with open(archive_path, 'w', encoding='utf-8') as f:
                            f.writelines(new_lines)
                        self.root.after(0, lambda: self.log_message(f"Removed {removed_count} video(s) from download archive"))
                    except Exception as e:
                        self.root.after(0, lambda: self.log_message(f"Error updating archive: {e}", "WARNING"))
            
            # Batch file deletions
            deleted_files = 0
            for item_id, video_info in videos_to_reset:
                try:
                    # Determine possible file extensions based on quality
                    if video_info['quality'].startswith('Audio-'):
                        audio_format = video_info['quality'].split('-')[1]
                        if audio_format == 'default':
                            possible_extensions = ['.webm', '.m4a', '.aac', '.mp3', '.ogg', '.opus']
                        elif audio_format == 'best':
                            possible_extensions = ['.m4a', '.aac', '.webm', '.mp4']
                        else:
                            possible_extensions = ['.mp3']
                    else:
                        possible_extensions = ['.mp4', '.mkv', '.webm']
                    
                    # Try to find and delete files
                    title_safe = re.sub(r'[<>:"/\\|?*]', '_', video_info['title'])
                    for ext in possible_extensions:
                        potential_file = os.path.join(download_path, f"{title_safe}{ext}")
                        if os.path.exists(potential_file):
                            os.remove(potential_file)
                            deleted_files += 1
                            self.root.after(0, lambda filename=os.path.basename(potential_file): 
                                          self.log_message(f"Deleted existing file: {filename}"))
                            break
                            
                except Exception as e:
                    self.root.after(0, lambda title=video_info['title'], error=str(e): 
                                  self.log_message(f"Error during reset for {title}: {error}", "WARNING"))
                
                # Update status to Pending on UI thread
                self.root.after(0, lambda id=item_id: self.update_video_status(id, 'Pending'))
            
            # Re-enable reset button and update UI on main thread
            def finish_reset():
                self.reset_button.config(state=tk.NORMAL)
                self.update_status_summary()
                self.schedule_save_settings()
                self.log_message(f"Reset {len(videos_to_reset)} video(s) to Pending status.")
                if deleted_files > 0:
                    self.log_message(f"Deleted {deleted_files} existing file(s).")
            
            self.root.after(0, finish_reset)
            
        except Exception as e:
            # Handle any unexpected errors
            def handle_error():
                self.reset_button.config(state=tk.NORMAL)
                self.log_message(f"Error during reset operation: {e}", "ERROR")
            
            self.root.after(0, handle_error)

    def update_reset_button_state(self):
        """Enable/disable reset button based on selection."""
        selected_items = self.tree.selection()
        resetable_count = 0
        
        for item_id in selected_items:
            current_values = self.tree.item(item_id, 'values')
            if len(current_values) >= 5:
                status = current_values[4]  # Status is back to index 4
                if status in ['Done', 'Failed', 'Skipped', 'QualityBlocked', 'AgeRestricted']:
                    resetable_count += 1
        
        if resetable_count > 0:
            self.reset_button.config(state=tk.NORMAL)
        else:
            self.reset_button.config(state=tk.DISABLED)

    def update_status_summary(self):
        """Update the status summary display with counts and colors."""
        if not hasattr(self, 'total_label'):
            return
            
        # Count statuses
        total = len(self.download_queue)
        done = sum(1 for v in self.download_queue if v.get('status') == 'Done')
        pending = sum(1 for v in self.download_queue if v.get('status', 'Pending') == 'Pending')
        failed = sum(1 for v in self.download_queue if v.get('status') == 'Failed')
        skipped = sum(1 for v in self.download_queue if v.get('status') == 'Skipped')
        quality_blocked = sum(1 for v in self.download_queue if v.get('status') == 'QualityBlocked')
        age_restricted = sum(1 for v in self.download_queue if v.get('status') == 'AgeRestricted')
        downloading = sum(1 for v in self.download_queue if v.get('status') == 'Downloading')
        
        # Update individual colored labels
        self.total_label.config(text=f"Total: {total}")
        self.done_label.config(text=f"Done: {done}")
        self.pending_label.config(text=f"Pending: {pending}")
        self.failed_label.config(text=f"Failed: {failed}")
        self.skipped_label.config(text=f"Skipped: {skipped}")
        self.quality_blocked_label.config(text=f"QualityBlocked: {quality_blocked}")
        self.age_restricted_label.config(text=f"AgeRestricted: {age_restricted}")
        
        # Show/hide downloading label based on whether there are downloading items
        if downloading > 0:
            self.downloading_label.config(text=f"Downloading: {downloading}")
            self.downloading_label.pack(side=tk.LEFT, padx=(0, 10))
        else:
            self.downloading_label.pack_forget()

    def classify_download_error(self, error_message, video_info):
        """Classify download errors and return appropriate status."""
        error_lower = error_message.lower()
        
        # Check for HTTP 403 Forbidden errors
        if "http error 403" in error_lower or "403: forbidden" in error_lower:
            self.log_message(f"HTTP 403 Forbidden detected for {video_info['title']} - Quality may be blocked", "WARNING")
            
            # Try to auto-retry with a different quality
            if self.auto_retry_with_different_quality(video_info):
                return 'Pending'  # Reset to pending for retry
            else:
                return 'QualityBlocked'
        
        # Check for age restriction errors
        if any(phrase in error_lower for phrase in [
            "age restricted", "age-restricted", "sign in to confirm your age",
            "this video may be inappropriate", "content warning",
            "requires age verification", "age gate"
        ]):
            self.log_message(f"Age restriction detected for {video_info['title']}", "WARNING")
            return 'AgeRestricted'
        
        # Check for other specific error patterns
        if "unavailable" in error_lower and "private" in error_lower:
            return 'Failed'
        
        if "region" in error_lower and ("blocked" in error_lower or "restricted" in error_lower):
            return 'Failed'
        
        # Default to Failed for other errors
        return 'Failed'

    def auto_retry_with_different_quality(self, video_info):
        """Automatically retry with a different quality when 403 error occurs."""
        current_quality = video_info['quality']
        
        # Handle audio format fallbacks
        if current_quality.startswith('Audio-'):
            audio_format = current_quality.split('-')[1]
            # Audio format fallback hierarchy: best → default (no more fallbacks after default)
            audio_fallback = {
                'best': 'default'
            }
            
            fallback_format = audio_fallback.get(audio_format)
            if fallback_format:
                fallback_quality = f'Audio-{fallback_format}'
                self.log_message(f"Auto-retrying {video_info['title']} with audio format: {current_quality} → {fallback_quality}", "INFO")
                video_info['quality'] = fallback_quality
                
                # Update GUI to show the new quality
                self.root.after(0, self.update_video_quality_in_gui, video_info['item_id'], fallback_quality)
                return True
            
            return False  # No more audio fallbacks available
        
        # Video quality fallback hierarchy
        quality_fallback = {
            'Best': '1080p',
            '1080p': '720p', 
            '720p': '480p',
            '480p': '360p',
            '360p': 'Audio-default'  # Final fallback to default audio
        }
        
        fallback_quality = quality_fallback.get(current_quality)
        if fallback_quality:
            self.log_message(f"Auto-retrying {video_info['title']} with quality: {current_quality} → {fallback_quality}", "INFO")
            video_info['quality'] = fallback_quality
            
            # Update GUI to show the new quality
            self.root.after(0, self.update_video_quality_in_gui, video_info['item_id'], fallback_quality)
            return True
        
        return False

    def suggest_troubleshooting(self, error_message):
        """Provide troubleshooting suggestions for common download errors."""
        error_lower = error_message.lower()
        
        if "postprocessing" in error_lower and "invalid data found when processing input" in error_lower:
            self.log_message("TROUBLESHOOTING: Postprocessing error detected. This usually happens when:", "WARNING")
            self.log_message("1. The video stream is corrupted or incomplete", "INFO")
            self.log_message("2. FFmpeg cannot merge the video and audio streams", "INFO")
            self.log_message("3. The video format is not compatible with the selected quality", "INFO")
            self.log_message("4. FFmpeg version is outdated or incompatible", "INFO")
            self.log_message("SOLUTIONS:", "WARNING")
            self.log_message("• Update FFmpeg to the latest version (see: https://github.com/yt-dlp/yt-dlp/issues/7541)", "INFO")
            self.log_message("• Try downloading as Audio Only (mp3) instead", "INFO")
            self.log_message("• Select a lower quality (720p or 480p)", "INFO")
            self.log_message("• Check if FFmpeg is properly installed and updated", "INFO")
            self.log_message("• The video might be region-restricted or have DRM protection", "INFO")
            self.log_message("• Try again later - the issue might be temporary", "INFO")
            
        elif "unavailable" in error_lower or "private" in error_lower:
            self.log_message("TROUBLESHOOTING: Video unavailable. Possible causes:", "WARNING")
            self.log_message("• Video is private, deleted, or region-restricted", "INFO")
            self.log_message("• Video requires age verification", "INFO")
            self.log_message("• Temporary YouTube server issues", "INFO")
            
        elif "format" in error_lower and "not available" in error_lower:
            self.log_message("TROUBLESHOOTING: Format not available. Try:", "WARNING")
            self.log_message("• Selecting a different quality option", "INFO")
            self.log_message("• Using Audio Only mode", "INFO")
            self.log_message("• The video might not have the requested quality", "INFO")
            
        elif "network" in error_lower or "connection" in error_lower or "timeout" in error_lower:
            self.log_message("TROUBLESHOOTING: Network issue detected. Try:", "WARNING")
            self.log_message("• Check your internet connection", "INFO")
            self.log_message("• Retry the download", "INFO")
            self.log_message("• Use a VPN if the content is region-blocked", "INFO")
            
        elif "ffmpeg" in error_lower:
            self.log_message("TROUBLESHOOTING: FFmpeg error. Solutions:", "WARNING")
            self.log_message("• Ensure FFmpeg is installed and in your PATH", "INFO")
            self.log_message("• Update FFmpeg to the latest version", "INFO")
            
        elif "http error 403" in error_lower or "403: forbidden" in error_lower:
            self.log_message("TROUBLESHOOTING: HTTP 403 Forbidden - Quality may be blocked. Try:", "WARNING")
            self.log_message("• Select a different quality (try 'Best' or lower quality)", "INFO")
            self.log_message("• Use Audio Only mode instead", "INFO")
            self.log_message("• The specific quality/format may be restricted for this video", "INFO")
            self.log_message("• Try again later - YouTube may have temporary restrictions", "INFO")
            self.log_message("• Some videos have quality-specific access restrictions", "INFO")
            
        elif "requested format is not available" in error_lower:
            self.log_message("TROUBLESHOOTING: Format not available - YouTube SABR protocol issue. Try:", "WARNING")
            self.log_message("• This is due to YouTube's new SABR streaming protocol (2025)", "INFO")
            self.log_message("• The app automatically uses android client to work around this", "INFO")
            self.log_message("• Try selecting a lower quality (720p, 480p, or 360p)", "INFO")
            self.log_message("• Use Audio Only mode for better compatibility", "INFO")
            self.log_message("• Update yt-dlp to the latest version", "INFO")
            
        elif any(phrase in error_lower for phrase in [
            "age restricted", "age-restricted", "sign in to confirm your age",
            "this video may be inappropriate", "content warning",
            "requires age verification", "age gate"
        ]):
            self.log_message("TROUBLESHOOTING: Age Restricted content detected:", "WARNING")
            self.log_message("• This video requires age verification on YouTube", "INFO")
            self.log_message("• Age-restricted videos cannot be downloaded without authentication", "INFO")
            self.log_message("• YouTube's age verification system blocks automated downloads", "INFO")
            self.log_message("• Consider using a different video or check if it's available elsewhere", "INFO")
            self.log_message("• Try downloading as Audio Only to bypass video processing", "INFO")

    def progress_hook(self, d):
        # Check if stop was requested during download and actively cancel
        if self.stop_event.is_set() and d.get('status') in ('downloading', 'processing'):
            if not self.stop_message_logged:
                self.progress_queue.put({'status': 'stop_requested'})
                self.stop_message_logged = True
                # Log the cancellation attempt with timestamp
                self.progress_queue.put({'status': 'cancellation_attempt', 'phase': d.get('status', 'unknown')})
            # Raise cancellation exception to immediately stop yt-dlp
            raise yt_dlp.utils.DownloadCancelled('User requested stop')
        self.progress_queue.put(d)

    def process_progress_queue(self):
        """Processes progress updates from the queue and displays them in the console."""
        try:
            while not self.progress_queue.empty():
                d = self.progress_queue.get_nowait()
                if d['status'] == 'stop_requested':
                    self.log_message("PROGRESS: Stop requested - waiting for current download to complete...", "WARNING")
                elif d['status'] == 'cancellation_attempt':
                    phase = d.get('phase', 'unknown')
                    self.log_message(f"PROGRESS: Attempting to cancel yt-dlp during {phase} phase", "WARNING")
                elif d['status'] == 'downloading':
                    current_time = time.time()
                    # Only update progress every 5 seconds for better user feedback
                    if current_time - self.last_progress_time >= 5:
                        percent_str = self.clean_ansi_codes(d.get('_percent_str', '0.0%').strip())
                        speed_str = self.clean_ansi_codes(d.get('_speed_str', 'N/A').strip())
                        eta_str = self.clean_ansi_codes(d.get('_eta_str', 'N/A').strip())
                        message = f"Downloading... {percent_str} | Speed: {speed_str} | ETA: {eta_str}"
                        self.log_message(message, overwrite=True)
                        self.last_progress_time = current_time
                elif d['status'] == 'finished':
                    # Add a final "100%" message before finalizing
                    self.log_message("Downloading... 100.0%", overwrite=True)
                    self.log_message("Finalizing download...", overwrite=False)
                    self.last_progress_time = 0  # Reset for next download
        except Exception: 
            pass # Ignore if queue is empty
        finally: 
            self.root.after(200, self.process_progress_queue) # Poll every 200ms

    def process_message_queue(self):
        """Processes yt-dlp messages from the queue and displays them in the console."""
        try:
            while not self.message_queue.empty():
                message_data = self.message_queue.get_nowait()
                # Only process the message if debug is enabled (check on GUI thread)
                if self.yt_dlp_debug_var.get():
                    self.log_message(message_data['message'], message_data['level'])
        except Exception:
            pass  # Ignore if queue is empty or other errors
        finally:
            self.root.after(100, self.process_message_queue)  # Poll every 100ms for more responsive logging

    def clean_ansi_codes(self, text):
        """Remove ANSI color codes from text."""
        # Remove ANSI escape sequences like [0;94m, [0m, etc.
        ansi_escape = re.compile(r'\x1b\[[0-9;]*m|\[[0-9;]*m')
        return ansi_escape.sub('', text)

    def log_message(self, msg, level='INFO', overwrite=False):
        """Logs a message to the console widget with log level filtering."""
        # Define log level hierarchy
        log_levels = {'DEBUG': 0, 'INFO': 1, 'WARNING': 2, 'ERROR': 3, 'CRITICAL': 4}
        current_level = log_levels.get(self.log_level_var.get(), 1)
        message_level = log_levels.get(level.upper(), 1)
        
        # Only show messages at or above the current log level
        if message_level < current_level:
            return
            
        self.console.config(state=tk.NORMAL)

        # Add timestamp for stop-related messages or when level is WARNING/ERROR
        timestamp = ""
        if level.upper() in ['WARNING', 'ERROR'] or 'stop' in msg.lower() or 'cancel' in msg.lower():
            import datetime
            now = datetime.datetime.now()
            timestamp = f"[{now.strftime('%H:%M:%S.%f')[:-3]}] "

        # Add level prefix to message
        if level.upper() != 'INFO':
            formatted_msg = f"{timestamp}[{level.upper()}] {msg}"
        else:
            formatted_msg = f"{timestamp}{msg}"

        if overwrite:
            # Check if the last line is a progress line. If so, delete it.
            current_last_line = self.console.get("end-1l linestart", "end-1c")
            if current_last_line.startswith("Downloading...") or current_last_line.startswith("[INFO] Downloading..."):
                self.console.delete("end-1l", "end")

            self.console.insert("end", formatted_msg)
        else:
            # For a normal message, check if the previous line was a progress update.
            current_last_line = self.console.get("end-1l linestart", "end-1c")
            if current_last_line.startswith("Downloading...") or current_last_line.startswith("[INFO] Downloading..."):
                self.console.delete("end-1l", "end")

            self.console.insert("end", formatted_msg + "\n")

        self.console.see(tk.END)
        self.console.config(state=tk.DISABLED)


    def update_button_states(self):
        """Enables/disables buttons based on the application's state."""
        state = tk.DISABLED if self.is_downloading else tk.NORMAL
        self.start_button.config(state=state)
        self.remove_button.config(state=state)
        self.clear_all_button.config(state=state)
        self.move_up_button.config(state=state)
        self.move_down_button.config(state=state)
        self.add_button.config(state=state)
        self.change_path_button.config(state=state)
        self.clear_logs_button.config(state=tk.NORMAL)  # Clear logs button is always enabled
        if self.is_downloading:
            self.stop_button.config(state=tk.NORMAL, text="⏹")
        else:
            self.stop_button.config(state=tk.DISABLED, text="⏹")
        
        # Reset button is handled separately by update_reset_button_state
        if not self.is_downloading:
            self.update_reset_button_state()
            self.update_status_summary()

    # --- SABR Bypass Mode Functions ---
    
    def detect_sabr_mode(self, test_url):
        """
        Detect if YouTube SABR is enforced using yt-dlp web client probe.
        Returns: (is_sabr_detected: bool, detection_details: dict)
        """
        try:
            # Use print for debugging in test scenarios where GUI might not be available
            try:
                self.log_message("Checking for SABR restrictions...", "DEBUG")
            except:
                print("Checking for SABR restrictions...")
            
            detection_details = {
                'test_url': test_url,
                'web_client_sabr': False,
                'tv_client_working': False,
                'warnings_detected': [],
                'timestamp': time.time(),
                'detection_method': 'web_client_probe'
            }
            
            # First, check if we can detect SABR from recent warnings in the current session
            # This is faster and can catch SABR symptoms from normal operations
            recent_sabr_detected = self.check_recent_warnings_for_sabr()
            if recent_sabr_detected:
                detection_details['web_client_sabr'] = True
                detection_details['detection_method'] = 'recent_warnings'
                detection_details['warnings_detected'] = ['PO Token warnings detected in recent operations']
                try:
                    self.log_message("SABR detected from recent PO Token warnings", "DEBUG")
                except:
                    print("SABR detected from recent PO Token warnings")
                
                # Still check TV client as control
                try:
                    detection_details['tv_client_working'] = self.quick_tv_client_check(test_url)
                except:
                    detection_details['tv_client_working'] = False
                
                is_sabr_detected = True
                try:
                    self.log_message("SABR restrictions detected from recent warnings - switching to bypass mode", "INFO")
                except:
                    print("SABR restrictions detected from recent warnings - switching to bypass mode")
                
                return is_sabr_detected, detection_details
            
            # Test using the same client configuration as actual downloads
            # This ensures SABR detection matches what happens during downloads
            detection_ydl_opts = {
                'quiet': True,
                'skip_download': True,
                'extractor_args': self.build_extractor_args(),  # Use same config as downloads
                'no_warnings': False
            }
            
            detection_warnings = []
            
            class SabrDetectionLogger:
                def debug(self, msg): pass
                def info(self, msg): pass
                def warning(self, msg): 
                    detection_warnings.append(msg)
                def error(self, msg): 
                    detection_warnings.append(msg)
                def to_screen(self, msg): pass
            
            try:
                with yt_dlp.YoutubeDL(detection_ydl_opts) as ydl:
                    ydl.params['logger'] = SabrDetectionLogger()
                    info = ydl.extract_info(test_url, download=False)
                    formats = info.get('formats', [])
                    
                    # Check for HTTPS formats with direct URLs
                    https_formats_with_url = [
                        f for f in formats 
                        if f.get('url', '').startswith('https://') and 'signatureCipher' not in f
                    ]
                    
                    # Check for SABR warning messages and PO Token warnings (which indicate SABR restrictions)
                    sabr_warnings = [
                        w for w in detection_warnings 
                        if any(keyword in w.lower() for keyword in [
                            'sabr', 'missing a url', 'forcing sabr', 
                            'po token', 'gvs po token', 'require a gvs po token',
                            'android client https formats require a gvs po token',
                            'ios client https formats require a gvs po token',
                            'android client sabr formats require',
                            'ios client sabr formats require'
                        ])
                    ]
                    
                    detection_details['warnings_detected'] = sabr_warnings
                    
                    # SABR detected if we get PO Token warnings (primary indicator)
                    # OR if no HTTPS formats with direct URLs
                    sabr_detected_by_warnings = len(sabr_warnings) > 0
                    sabr_detected_by_formats = len(https_formats_with_url) == 0
                    
                    if sabr_detected_by_warnings or sabr_detected_by_formats:
                        detection_details['web_client_sabr'] = True
                        try:
                            self.log_message(f"SABR detected: {len(sabr_warnings)} warnings, {len(https_formats_with_url)} HTTPS formats", "DEBUG")
                        except:
                            print(f"SABR detected: {len(sabr_warnings)} warnings, {len(https_formats_with_url)} HTTPS formats")
                    else:
                        try:
                            self.log_message(f"No SABR detected: {len(sabr_warnings)} warnings, {len(https_formats_with_url)} HTTPS formats available", "DEBUG")
                        except:
                            print(f"No SABR detected: {len(sabr_warnings)} warnings, {len(https_formats_with_url)} HTTPS formats available")
                        
            except Exception as e:
                try:
                    self.log_message(f"SABR detection check failed: {e}", "DEBUG")
                except:
                    print(f"SABR detection check failed: {e}")
                detection_details['web_client_sabr'] = False
            
            # Test TV client as control (should still work)
            tv_ydl_opts = {
                'quiet': True,
                'skip_download': True,
                'extractor_args': {'youtube': {'player_client': ['tv']}},
                'no_warnings': True
            }
            
            try:
                with yt_dlp.YoutubeDL(tv_ydl_opts) as ydl:
                    info = ydl.extract_info(test_url, download=False)
                    formats = info.get('formats', [])
                    
                    # Check if TV client has working HTTPS formats
                    tv_https_formats = [
                        f for f in formats 
                        if f.get('url', '').startswith('https://')
                    ]
                    
                    if len(tv_https_formats) > 0:
                        detection_details['tv_client_working'] = True
                        try:
                            self.log_message(f"TV client working: {len(tv_https_formats)} HTTPS formats available", "DEBUG")
                        except:
                            print(f"TV client working: {len(tv_https_formats)} HTTPS formats available")
                    else:
                        try:
                            self.log_message("TV client also restricted", "DEBUG")
                        except:
                            print("TV client also restricted")
                        
            except Exception as e:
                try:
                    self.log_message(f"TV client check failed: {e}", "DEBUG")
                except:
                    print(f"TV client check failed: {e}")
                detection_details['tv_client_working'] = False
            
            # SABR is detected if web client shows SABR symptoms
            is_sabr_detected = detection_details['web_client_sabr']
            
            if is_sabr_detected:
                try:
                    self.log_message("SABR restrictions detected - switching to bypass mode", "INFO")
                except:
                    print("SABR restrictions detected - switching to bypass mode")
            else:
                try:
                    self.log_message("No SABR restrictions detected - using normal mode", "DEBUG")
                except:
                    print("No SABR restrictions detected - using normal mode")
            
            return is_sabr_detected, detection_details
            
        except Exception as e:
            try:
                self.log_message(f"SABR detection failed: {e}", "ERROR")
            except:
                print(f"SABR detection failed: {e}")
            return False, {'error': str(e), 'timestamp': time.time()}
    
    def activate_sabr_mode(self, detection_details):
        """Activate SABR bypass mode with restricted quality options."""
        self.log_message(f"ACTIVATING SABR MODE - Detection method: {detection_details.get('detection_method', 'unknown')}", "DEBUG")
        self.sabr_mode_active = True
        self.sabr_detection_details = detection_details
        self.last_sabr_check = time.time()
        
        # Update quality dropdowns to restricted options
        self.update_quality_options_for_sabr()
        
        # Show SABR indicator
        self.show_sabr_indicator()
        
        # Hide both SABR control buttons since SABR is now active
        # The Re-Check SABR button in the indicator serves the same purpose
        self.log_message("Hiding SABR control buttons...", "DEBUG")
        if hasattr(self, 'force_sabr_button'):
            self.force_sabr_button.pack_forget()
            self.log_message("Force SABR button hidden", "DEBUG")
        if hasattr(self, 'manual_sabr_button'):
            self.manual_sabr_button.pack_forget()
            self.log_message("Check SABR button hidden", "DEBUG")
        
        # Update existing queue items to compatible formats
        self.update_queue_for_sabr_mode()
        
        self.log_message("SABR Bypass Mode activated - quality options restricted", "INFO")
    
    def deactivate_sabr_mode(self):
        """Deactivate SABR bypass mode and restore full quality options."""
        self.log_message("Deactivating SABR Bypass Mode...", "DEBUG")
        self.sabr_mode_active = False
        self.sabr_detection_details = {}
        
        # Restore full quality options
        self.log_message("Restoring full quality options...", "DEBUG")
        self.restore_full_quality_options()
        
        # Hide SABR indicator
        self.log_message("Hiding SABR indicator...", "DEBUG")
        self.hide_sabr_indicator()
        
        # Show both SABR control buttons again since SABR is no longer active
        self.log_message("Showing SABR control buttons...", "DEBUG")
        if hasattr(self, 'manual_sabr_button'):
            self.manual_sabr_button.pack(side=tk.LEFT, padx=(0, 5))
            self.log_message("Check SABR button shown", "DEBUG")
        if hasattr(self, 'force_sabr_button'):
            self.force_sabr_button.pack(side=tk.LEFT, padx=(0, 5))
            self.log_message("Force SABR button shown", "DEBUG")
        
        self.log_message("SABR Bypass Mode deactivated - full quality options restored", "INFO")
    
    def update_quality_options_for_sabr(self):
        """Update quality dropdown menus for SABR mode restrictions."""
        # Update video quality options
        current_quality = self.quality_var.get()
        self.quality_menu['menu'].delete(0, 'end')
        
        for option in self.sabr_quality_options:
            self.quality_menu['menu'].add_command(label=option, command=tk._setit(self.quality_var, option))
        
        # Set to compatible quality if current selection is not available
        if current_quality not in self.sabr_quality_options:
            self.quality_var.set('360p')  # Only 360p works under SABR
        
        # Update audio format options
        current_audio = self.audio_format_var.get()
        self.audio_format_menu['menu'].delete(0, 'end')
        
        for option in self.sabr_audio_options:
            self.audio_format_menu['menu'].add_command(label=option, command=tk._setit(self.audio_format_var, option))
        
        # Set to compatible audio format if current selection is not available
        if current_audio not in self.sabr_audio_options:
            self.audio_format_var.set(self.sabr_audio_options[0])  # Default to standard_mp3
    
    def restore_full_quality_options(self):
        """Restore full quality dropdown options for normal mode."""
        # Restore video quality options
        current_quality = self.quality_var.get()
        self.quality_menu['menu'].delete(0, 'end')
        
        for option in self.original_quality_options:
            self.quality_menu['menu'].add_command(label=option, command=tk._setit(self.quality_var, option))
        
        # Restore previous quality if it was valid
        if current_quality not in self.original_quality_options:
            self.quality_var.set('1080p')  # Default back to 1080p
        
        # Restore audio format options
        current_audio = self.audio_format_var.get()
        self.audio_format_menu['menu'].delete(0, 'end')
        
        for option in self.original_audio_options:
            self.audio_format_menu['menu'].add_command(label=option, command=tk._setit(self.audio_format_var, option))
        
        # Restore previous audio format if it was valid
        if current_audio not in self.original_audio_options:
            self.audio_format_var.set('default (Auto)')  # Default back to auto
    
    def update_queue_for_sabr_mode(self):
        """Update existing queue items to use SABR-compatible formats."""
        updated_count = 0
        
        for video_info in self.download_queue:
            if video_info.get('status') in ['Done', 'Failed']:
                continue  # Skip completed/failed items
            
            original_quality = video_info.get('quality', '')
            
            # Update video quality if not compatible
            if not video_info['quality'].startswith('Audio-') and original_quality not in self.sabr_quality_options:
                video_info['quality'] = '360p'  # Only 360p works under SABR
                updated_count += 1
            
            # Update audio quality if not compatible
            elif video_info['quality'].startswith('Audio-'):
                audio_format = video_info['quality'].replace('Audio-', '')
                if audio_format not in [opt.split(' ')[0] for opt in self.sabr_audio_options]:
                    video_info['quality'] = 'Audio-standard_mp3'  # Default SABR audio quality
                    updated_count += 1
        
        if updated_count > 0:
            self.log_message(f"Updated {updated_count} queue items to SABR-compatible formats", "INFO")
            self.refresh_tree_display()
    
    def refresh_tree_display(self):
        """Refresh the tree display to show updated queue items."""
        # Clear and rebuild tree
        for item in self.tree.get_children():
            self.tree.delete(item)
        
        # Re-add all items
        for video in self.download_queue:
            item_id = self.tree.insert('', 'end', iid=video['item_id'], values=(
                self.format_video_id_with_icon(video.get('id', 'N/A')),
                video['title'],
                video['quality'],
                self.format_duration(video.get('duration')),
                video.get('status', 'Pending')
            ))
            
            # Apply status-based styling
            status = video.get('status', 'Pending')
            if status == 'Done':
                self.tree.item(item_id, tags=('done',))
            elif status == 'Failed':
                self.tree.item(item_id, tags=('failed',))
            elif status == 'Downloading':
                self.tree.item(item_id, tags=('downloading',))
            else:
                self.tree.item(item_id, tags=('pending',))
        
        self.update_status_summary()
        self.update_line_numbers()  # Update line numbers after refresh
    
    def show_sabr_indicator(self):
        """Show the SABR mode indicator widget."""
        if self.sabr_indicator_frame is not None:
            return  # Already showing
        
        # Use the dedicated SABR control frame
        if hasattr(self, 'sabr_control_frame'):
            # Create SABR indicator frame
            self.sabr_indicator_frame = ttk.Frame(self.sabr_control_frame)
            self.sabr_indicator_frame.pack(side=tk.LEFT, padx=(20, 0))
            
            # Red bolt icon
            sabr_icon = tk.Label(self.sabr_indicator_frame, text="⚡", fg="red", font=("Arial", 12, "bold"))
            sabr_icon.pack(side=tk.LEFT, padx=(0, 5))
            
            # SABR mode text
            sabr_text = tk.Label(self.sabr_indicator_frame, text="SABR Bypass Mode - quality reduced", fg="red", font=("Arial", 9))
            sabr_text.pack(side=tk.LEFT, padx=(0, 10))
            
            # Re-check button
            recheck_button = ttk.Button(self.sabr_indicator_frame, text="Re-Check SABR", command=self.recheck_sabr)
            recheck_button.pack(side=tk.LEFT)
    
    def hide_sabr_indicator(self):
        """Hide the SABR mode indicator widget."""
        if self.sabr_indicator_frame is not None:
            self.sabr_indicator_frame.destroy()
            self.sabr_indicator_frame = None
    
    def recheck_sabr(self):
        """Re-check SABR status and update mode accordingly."""
        if not self.download_queue:
            self.log_message("No videos in queue to test SABR detection", "WARNING")
            return
        
        # Use the first video in queue for testing
        test_url = self.download_queue[0].get('url', '')
        if not test_url:
            self.log_message("No valid URL found for SABR re-check", "WARNING")
            return
        
        self.log_message("Re-checking SABR status...", "INFO")
        
        # Run detection in background thread to avoid blocking UI
        def run_recheck():
            try:
                is_sabr_detected, detection_details = self.detect_sabr_mode(test_url)
                
                # Update UI on main thread
                self.root.after(0, self.handle_sabr_recheck_result, is_sabr_detected, detection_details)
            except Exception as e:
                self.root.after(0, lambda: self.log_message(f"SABR re-check failed: {e}", "ERROR"))
        
        threading.Thread(target=run_recheck, daemon=True).start()
    
    def handle_sabr_recheck_result(self, is_sabr_detected, detection_details):
        """Handle the result of SABR re-check on the main thread."""
        self.log_message(f"SABR recheck result: detected={is_sabr_detected}, current_mode_active={self.sabr_mode_active}", "DEBUG")
        
        if is_sabr_detected and not self.sabr_mode_active:
            # SABR detected but not in bypass mode - activate it
            self.log_message("SABR detected but not in bypass mode - activating", "DEBUG")
            self.activate_sabr_mode(detection_details)
        elif not is_sabr_detected and self.sabr_mode_active:
            # SABR not detected but in bypass mode - deactivate it
            self.log_message("SABR not detected but in bypass mode - deactivating", "DEBUG")
            self.deactivate_sabr_mode()
        elif is_sabr_detected and self.sabr_mode_active:
            # Still in SABR mode - update detection details
            self.sabr_detection_details = detection_details
            self.last_sabr_check = time.time()
            self.log_message("SABR still detected - remaining in bypass mode", "INFO")
        else:
            # Not in SABR mode and no SABR detected - no change needed
            self.log_message("No SABR detected - remaining in normal mode", "INFO")
    
    def check_recent_warnings_for_sabr(self):
        """Check recent log messages for SABR indicators like PO Token warnings."""
        # Look for SABR indicators in recent operations
        # This is a heuristic based on common SABR symptoms
        
        # Check if we have a console widget with recent messages
        if hasattr(self, 'console') and hasattr(self.console, 'get'):
            try:
                recent_logs = self.console.get('1.0', 'end').lower()
                sabr_indicators = [
                    'po token', 'gvs po token', 'require a gvs po token',
                    'sabr formats require', 'android client sabr formats',
                    'ios client sabr formats', 'https formats require a gvs po token',
                    'android client https formats require a gvs po token',
                    'ios client https formats require a gvs po token'
                ]
                
                for indicator in sabr_indicators:
                    if indicator in recent_logs:
                        print(f"SABR indicator found in logs: {indicator}")
                        return True
            except Exception as e:
                print(f"Error checking console logs: {e}")
        
        # Also check if we're seeing quality auto-adjustments to low resolutions
        # This is another strong SABR indicator
        if hasattr(self, 'console') and hasattr(self.console, 'get'):
            try:
                recent_logs = self.console.get('1.0', 'end').lower()
                if 'quality auto-adjusted' in recent_logs and '360p' in recent_logs:
                    print("SABR indicator: Quality auto-adjusted to 360p detected")
                    return True
            except:
                pass
        
        return False
    
    def quick_tv_client_check(self, test_url):
        """Quick check if TV client has working formats."""
        try:
            tv_ydl_opts = {
                'quiet': True,
                'skip_download': True,
                'extractor_args': {'youtube': {'player_client': ['tv']}},
                'no_warnings': True
            }
            
            with yt_dlp.YoutubeDL(tv_ydl_opts) as ydl:
                info = ydl.extract_info(test_url, download=False)
                formats = info.get('formats', [])
                
                # Check if TV client has working HTTPS formats
                tv_https_formats = [
                    f for f in formats 
                    if f.get('url', '').startswith('https://')
                ]
                
                return len(tv_https_formats) > 0
        except:
            return False
    
    def trigger_sabr_detection(self, test_url):
        """Trigger SABR detection in background thread."""
        if not test_url:
            return
        
        def run_detection():
            try:
                is_sabr_detected, detection_details = self.detect_sabr_mode(test_url)
                
                # Update UI on main thread
                self.root.after(0, self.handle_sabr_detection_result, is_sabr_detected, detection_details)
            except Exception as e:
                self.root.after(0, lambda: self.log_message(f"SABR detection failed: {e}", "ERROR"))
        
        threading.Thread(target=run_detection, daemon=True).start()
    
    def handle_sabr_detection_result(self, is_sabr_detected, detection_details):
        """Handle SABR detection result on the main thread."""
        if is_sabr_detected and not self.sabr_mode_active:
            self.activate_sabr_mode(detection_details)
        elif not is_sabr_detected:
            self.last_sabr_check = time.time()  # Mark that we checked
    
    def activate_sabr_from_warning(self, warning_msg):
        """Activate SABR mode immediately when detected from yt-dlp warning."""
        if self.sabr_mode_active:
            return  # Already in SABR mode
        
        detection_details = {
            'test_url': 'detected_from_warning',
            'web_client_sabr': True,
            'tv_client_working': False,  # Unknown
            'warnings_detected': [warning_msg],
            'timestamp': time.time(),
            'detection_method': 'realtime_warning'
        }
        
        self.log_message(f"SABR detected from yt-dlp warning: {warning_msg[:100]}...", "INFO")
        self.activate_sabr_mode(detection_details)
    
    def manual_sabr_check(self):
        """Manual SABR check triggered by user button - same as re-check but works from any state."""
        if not self.download_queue:
            self.log_message("No videos in queue - adding test URL for SABR check", "INFO")
            # Use a reliable test URL
            test_url = "https://www.youtube.com/watch?v=dQw4w9WgXcQ"
        else:
            test_url = self.download_queue[0].get('url', '')
        
        if not test_url:
            self.log_message("No valid URL found for SABR check", "WARNING")
            return
        
        self.log_message("Manual SABR check initiated...", "INFO")
        
        # Run detection in background thread to avoid blocking UI
        def run_manual_check():
            try:
                is_sabr_detected, detection_details = self.detect_sabr_mode(test_url)
                
                # Update UI on main thread using the same logic as re-check
                self.root.after(0, self.handle_sabr_recheck_result, is_sabr_detected, detection_details)
            except Exception as e:
                self.root.after(0, lambda: self.log_message(f"Manual SABR check failed: {e}", "ERROR"))
        
        threading.Thread(target=run_manual_check, daemon=True).start()
    
    def force_sabr_mode(self):
        """Force activate SABR mode immediately (for testing when SABR is clearly active)."""
        if self.sabr_mode_active:
            self.log_message("SABR mode is already active", "INFO")
            return
        
        detection_details = {
            'test_url': 'forced_activation',
            'web_client_sabr': True,
            'tv_client_working': False,
            'warnings_detected': ['Manually forced due to visible SABR symptoms'],
            'timestamp': time.time(),
            'detection_method': 'manual_force'
        }
        
        self.log_message("Forcing SABR Bypass Mode activation...", "INFO")
        self.activate_sabr_mode(detection_details)

    def schedule_save_settings(self):
        """Schedule a delayed save to avoid I/O churn during bulk operations."""
        if hasattr(self, '_save_settings_after_id') and self._save_settings_after_id:
            self.root.after_cancel(self._save_settings_after_id)
        self._save_settings_after_id = self.root.after(1000, self.save_settings)  # Save after 1 second delay

    def _insert_videos_chunked(self, videos, chunk_size=300):
        """Insert videos in chunks to keep UI responsive during bulk operations."""
        if not videos:
            self.update_status_summary()
            self.schedule_save_settings()
            return
        
        batch, rest = videos[:chunk_size], videos[chunk_size:]
        for video in batch:
            duration = video.get('duration', 'N/A')
            status = video.get('status', 'Pending')
            item_id = self.tree.insert('', tk.END, values=(self.format_video_id_with_icon(video['id']), video['title'], video['quality'], duration, status), tags=('pending',))
            video['item_id'] = item_id
            video['status'] = status
            self.download_queue.append(video)
            
            # Set appropriate color tag based on status
            if status == 'Downloading':
                self.tree.item(item_id, tags=('downloading',))
            elif status == 'Done':
                self.tree.item(item_id, tags=('done',))
            elif status == 'Failed':
                self.tree.item(item_id, tags=('failed',))
            elif status == 'Skipped':
                self.tree.item(item_id, tags=('skipped',))
            else:
                self.tree.item(item_id, tags=('pending',))
        
        self.update_status_summary()
        if rest:
            self.root.after(0, lambda: self._insert_videos_chunked(rest, chunk_size))
        else:
            self.update_line_numbers()  # Update line numbers after all videos are inserted
            self.schedule_save_settings()

    def save_settings(self):
        """Saves download path, log level, debug setting, and queue to the settings file."""
        try:
            settings = {
                'download_path': self.download_path.get(),
                'log_level': self.log_level_var.get(),
                'audio_format': self.audio_format_var.get(),
                'yt_dlp_debug': self.yt_dlp_debug_var.get(),
                'console_visible': self.console_visible_var.get(),
                'queue': [{k: v for k, v in video.items() if k not in ['item_id', 'info']} for video in self.download_queue],  # Exclude 'info' from saving
                'sabr_mode': {
                    'active': self.sabr_mode_active,
                    'last_check': self.last_sabr_check,
                    'detection_details': self.sabr_detection_details
                },
                'cookie_auth': {
                    'mode': self.cookie_mode.get(),
                    'browser': self.cookie_browser.get(),
                    'browser_profile': self.cookie_browser_profile.get(),
                    'file_path': self.cookie_file_path.get()
                }
            }
            with open(SETTINGS_FILE, 'w') as f:
                json.dump(settings, f, indent=4)
        except Exception as e:
            print(f"Error saving settings: {e}")

    def load_settings(self):
        """Loads settings from the settings file on startup."""
        if os.path.exists(SETTINGS_FILE):
            try:
                with open(SETTINGS_FILE, 'r') as f:
                    settings = json.load(f)
                
                path = settings.get('download_path', DEFAULT_DOWNLOAD_PATH)
                self.download_path.set(path)

                # Load log level setting
                log_level = settings.get('log_level', 'INFO')
                self.log_level_var.set(log_level)
                
                # Load audio format setting
                audio_format = settings.get('audio_format', 'default (YouTube)')
                self.audio_format_var.set(audio_format)
                
                # Load yt-dlp debug setting
                yt_dlp_debug = settings.get('yt_dlp_debug', False)
                self.yt_dlp_debug_var.set(yt_dlp_debug)
                
                # Load console visibility setting
                console_visible = settings.get('console_visible', True)
                self.console_visible_var.set(console_visible)
                # Apply the console visibility setting
                if not console_visible:
                    self.console.pack_forget()
                
                # Load SABR mode settings (but don't auto-restore SABR mode)
                # SABR mode should only be activated by user actions, not on startup
                sabr_settings = settings.get('sabr_mode', {})
                self.sabr_mode_active = False  # Always start with SABR mode disabled
                self.last_sabr_check = sabr_settings.get('last_check', None)
                self.sabr_detection_details = sabr_settings.get('detection_details', {})
                
                self.log_message("SABR mode starts disabled - will be activated only by user actions", "DEBUG")
                
                # Load cookie authentication settings
                cookie_settings = settings.get('cookie_auth', {})
                cookie_mode = cookie_settings.get('mode', 'none')
                self.cookie_browser.set(cookie_settings.get('browser', 'chrome'))
                self.cookie_browser_profile.set(cookie_settings.get('browser_profile', ''))
                self.cookie_file_path.set(cookie_settings.get('file_path', ''))
                # Apply cookie mode (this shows/hides the right widgets)
                self._set_cookie_mode(cookie_mode)

                loaded_queue = settings.get('queue', [])
                if loaded_queue:
                    # Ensure duration and status fields exist for backward compatibility
                    for video in loaded_queue:
                        if 'duration' not in video:
                            video['duration'] = 'N/A'
                        if 'status' not in video:
                            video['status'] = 'Pending'
                    self.add_videos_to_gui(loaded_queue)
                    self.log_message(f"Loaded {len(loaded_queue)} items and settings from previous session.")
                else:
                    # Initialize status summary even with empty queue
                    self.update_status_summary()
            except Exception as e:
                self.log_message(f"Could not load settings: {e}", "ERROR")
                self.update_status_summary()  # Initialize status summary on error
        else:
            # Initialize status summary for first run
            self.update_status_summary()

    def on_closing(self):
        """Handles the window closing event."""
        if self.is_downloading:
            if messagebox.askyesno("Exit", "A download is in progress. Are you sure you want to exit?"):
                self.stop_event.set()
                self.save_settings()
                self.root.destroy()
        else:
            self.save_settings()
            self.root.destroy()



def check_yt_dlp_on_startup():
    """Check if yt-dlp is available and suggest installation if not."""
    # First try importing the Python module (what the app actually uses)
    try:
        import yt_dlp
        if hasattr(yt_dlp, 'version') and hasattr(yt_dlp.version, '__version__'):
            print(f"yt-dlp version: {yt_dlp.version.__version__} (Python module)")
            return True
        elif hasattr(yt_dlp, '__version__'):
            print(f"yt-dlp version: {yt_dlp.__version__} (Python module)")
            return True
    except ImportError:
        pass  # Will try CLI check below
    except Exception as e:
        print(f"Error checking yt-dlp Python module: {e}")
    
    # Fallback: try CLI executable
    try:
        result = subprocess.run(['yt-dlp', '--version'], 
                              capture_output=True, text=True, timeout=5)
        if result.returncode == 0:
            print(f"yt-dlp version: {result.stdout.strip()} (CLI)")
            return True
        else:
            print("WARNING: yt-dlp not found or not accessible")
            print("Please install yt-dlp with: pip install yt-dlp")
            return False
    except (FileNotFoundError, subprocess.TimeoutExpired):
        print("WARNING: yt-dlp not found in system PATH")
        print("Please install yt-dlp with: pip install yt-dlp")
        return False
    except Exception as e:
        print(f"Error checking yt-dlp: {e}")
        return False

def main():
    """Main function to run the application."""
    try:
        # Check yt-dlp availability on startup
        print("YouTube Downloader starting...")
        yt_dlp_available = check_yt_dlp_on_startup()
        
        if not yt_dlp_available:
            print("\nIMPORTANT: yt-dlp is required for this application to work.")
            print("Please install it using: pip install yt-dlp")
            print("The application will still start, but downloads will fail.")
            print("Press Enter to continue or Ctrl+C to exit...")
            try:
                input()
            except KeyboardInterrupt:
                print("\nExiting...")
                return 1
        
        # Create and run the app
        root = tk.Tk()
        app = YouTubeDownloaderApp(root)
        root.mainloop()
        
    except Exception as e:
        print(f"Error: {e}")
        return 1
    
    return 0

if __name__ == '__main__':
    main()

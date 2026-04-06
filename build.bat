@echo off
echo.
echo =======================================================
echo     YouTube Downloader Minimal Build Script
echo =======================================================
echo.

REM Set virtual environment directory
set VENV_DIR=venv_build

REM Clean everything
if exist "dist" rmdir /s /q "dist"
if exist "build" rmdir /s /q "build"
if exist "__pycache__" rmdir /s /q "__pycache__"
del *.spec 2>nul

echo Setting up virtual environment...
echo.

REM Create virtual environment if it doesn't exist
if not exist "%VENV_DIR%" (
    echo Creating virtual environment...
    python -m venv %VENV_DIR%
    if errorlevel 1 (
        echo ERROR: Failed to create virtual environment
        pause
        exit /b 1
    )
)

REM Activate virtual environment
echo Activating virtual environment...
call %VENV_DIR%\Scripts\activate.bat
if errorlevel 1 (
    echo ERROR: Failed to activate virtual environment
    pause
    exit /b 1
)

echo.
echo Upgrading pip...
python -m pip install --upgrade pip

echo.
echo Installing nightly yt-dlp with default dependencies...
pip install -U --pre "yt-dlp[default]"
if errorlevel 1 (
    echo ERROR: Failed to install yt-dlp
    pause
    exit /b 1
)

echo.
echo Installing PyInstaller...
pip install pyinstaller
if errorlevel 1 (
    echo ERROR: Failed to install PyInstaller
    pause
    exit /b 1
)

echo.
echo Verifying yt-dlp installation...
python -c "import yt_dlp; print(f'yt-dlp version: {yt_dlp.version.__version__}')"
if errorlevel 1 (
    echo ERROR: Failed to verify yt-dlp installation
    pause
    exit /b 1
)

echo.
echo Building minimal single-file version...
echo.

REM Absolute minimal build - just the essentials (no ffmpeg bundled)

pyinstaller ^
    --onefile ^
    --noconsole ^
    --name youtube_downloader ^
    --clean ^
    --noconfirm ^
    youtube_downloader.py

if exist "dist\youtube_downloader.exe" (
    echo.
    echo SUCCESS: Minimal build completed!
    echo Executable: dist\youtube_downloader.exe
    for %%A in ("dist\youtube_downloader.exe") do echo Size: %%~zA bytes
    echo.
    echo =======================================================
    echo                 IMPORTANT NOTICE
    echo =======================================================
    echo.
    echo FFmpeg is required but NOT included in this build.
    echo You must install FFmpeg separately for video processing.
    echo.
    echo INSTALLATION OPTIONS:
    echo.
    echo 1. AUTOMATIC ^(Recommended^):
    echo    winget install FFmpeg
    echo.
    echo 2. MANUAL DOWNLOAD:
    echo    - Download: https://github.com/BtbN/FFmpeg-Builds/releases
    echo    - Extract ffmpeg.exe to a folder
    echo    - Add that folder to your Windows PATH
    echo.
    echo 3. PORTABLE ^(Advanced^):
    echo    - Place ffmpeg.exe in the same folder as youtube_downloader.exe
    echo.
    echo VERIFY INSTALLATION:
    echo    Open Command Prompt and run: ffmpeg -version
    echo.
    echo The application will check FFmpeg availability on startup.
    echo =======================================================
) else (
    echo ERROR: Build failed.
    pause
    exit /b 1
)

echo.
echo Deactivating virtual environment...
deactivate

echo.
pause
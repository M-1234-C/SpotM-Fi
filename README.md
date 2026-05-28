# SpotM-Fi
This is an offline music player that recreates the popular online music service gui with full functionality

# Main Features
​Smart Search: Find songs in your folders and add them to your library.
​Custom Playlists: Create your own collections with custom titles and descriptions.
​Lyrics Editor: A built-in tool to write and save lyrics for any song and have it synced.
​Liked Songs: Heart your favorite tracks to save them in a special list.
​Hybrid Engine: Works on both Windows/Mac (Desktop) and Android phones.
​Auto-Save: All your playlists and lyrics are saved in a .json file.

​# Navigation 
​Sidebar: Switch between Home, Search, and your Playlists.
​Media Bar: Play, Pause, Shuffle, and Skip songs at the bottom of the screen.
​Progress Bar: Click anywhere on the bar to skip to a specific part of the song.
​Add Folder: Go to the Search tab to import your music folder.

# Help


# Installation

To run this app, you need to install the following libraries. Some are "backups" that help the app read special music formats or work on Android so if you want to decrease the space it takes up get the ones you only need but i recomend installing them all anyway.

### 1. Core Requirements (Must Install)
These are required for the app to open and play standard music:
* **Pygame**: `pip install pygame` (The main engine)
* **Mutagen**: `pip install mutagen` (Used to read song info like Artist and Duration)

### 2. Backup Libraries (For Full Support)
The app uses these to handle files like MP4, M4A, or AAC:
* **MoviePy**: `pip install moviepy` (Used to convert/extract audio from video files)
* **Pydub**: `pip install pydub` (Alternative audio processor)

### 3. Android Support (Mobile Only)
If you are building this for an Android phone, you will also need:
* **Pyjnius**: (Lets Python talk to the Android system)



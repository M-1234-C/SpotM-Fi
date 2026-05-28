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
​Playlist Covers: When you create a playlist, you can assign an image to it just find it in the directores page that opens when you click to change the cover. If you want to change it after you have created the playlist then go into it and click the cover and select you image just like you did before it support the formats: .png, .jpg, .jpeg.

​Default Icons: If no image is found, the app will use a default grey placeholder with a music note.
​Song Art: The app tries to read metadata. If your MP3 already has an album cover attached to it, SpotM-Fi will attempt to display it in the song box.(custom icon support will be added in future version)

Lyrics And Syncing: Open the Editor While a song is playing, look for the small paper icon
​a window will pop up. You can type directly into it or Paste lyrics you copied from the web.
​On Desktop, you can use Ctrl + V. On Android the built in clipbaord.But how to sync the lyrics as by itself nothing happens.To Sync them you have to put "[]" before each verse with the time it plays in it for example: "[1:23] Oh i love music" or "[0:06] let it snow, let it snow, let it snow" once you done this for each verse hit the Save button then when you play the song the lyrics are synced and show in the bpottom left of media when the verse is being sang if they have been timed right and all lyric are saved inisde the .json file so when you close it or force clsoe the app by acident they will still be their when you open it up again.
​
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



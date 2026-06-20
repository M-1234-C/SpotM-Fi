# SpotM-Fi
This is an offline music player that recreates the popular online msuic service with full functionality

# Main Features
- **Smart Search**: Browse your device storage, pick a folder, and import every supported audio file inside it into your library.
- **Custom Playlists**: Create your own collections with custom titles, descriptions, and cover art.
- **Liked Songs**: Heart your favorite tracks to save them in a special list.
- **Album Art**: Cover art embedded in your music files (MP3, FLAC, M4A, OGG) is detected and displayed automatically. You can also manually assign a custom image to any individual track, playlist, or your Liked Songs list.
- **Lyrics Editor**: A built-in tool to write, paste, or import lyrics for any song and have them synced to playback.
- **Hybrid Engine**: Runs on Windows/Mac (Desktop) and Android phones, with a layout that adapts to each.
- **Auto-Save**: Your playlists, liked songs, covers, and lyrics are all saved automatically to a local `.json` file.

# Navigation
- **Sidebar**: Switch between **Search**, **Your Library**, and **Settings**.
- **Media Bar**: Play, Pause, Skip, Shuffle, and jump back/forward 10 seconds, at the bottom of the screen.
- **Progress Bar**: Click (or tap and drag) anywhere on the bar to seek to a specific part of the song.
- **Settings**: Switch between Desktop and Phone layout, and manage your imported folders.
- **Add Folder**: Go to the Search tab and tap "+ Add Folder" to open the built-in storage browser and import a music folder.

<img width="2880" height="234" alt="1001161322" src="https://github.com/user-attachments/assets/33038ef4-912f-44b3-a016-152130fd9824" />

# Help

Playlist Covers: When you create a playlist, you can assign a cover image to it — just find it through the storage browser that opens when you click the cover. If you want to change it later, open the playlist and click the cover again to pick a new image. Supported formats: `.png`, `.jpg`, `.jpeg`.

The same applies to individual tracks: open a song in the media bar and tap the picture-frame icon to set or replace a custom cover for that track, overriding any embedded art.

<img width="2880" height="1800" alt="1001161327" src="https://github.com/user-attachments/assets/5eaefa00-e687-43bc-ad3d-c63240d74d51" />

Default Covers/Song Art: If a track has no embedded album art and no custom cover has been set, the app shows a plain placeholder box instead.Cover art embedded in the audio file's own metadata (ID3/FLAC/MP4 tags) is extracted and shown automatically wherever possible, no setup needed.

Lyrics & Syncing: Open the editor while a song is playing by tapping the small paper icon in the media bar. A window will pop up where you can:
- Type directly into it,
- Paste lyrics you've copied from the web (`Ctrl+V` on Desktop, the built-in clipboard on Android), or
- Import lyrics from a `.txt` file using the Import button, which opens the storage browser (Use SpotM-Fi-Lyrics-Finder in my repositories its made it for this use case).

By itself, plain text won't sync to anything — to sync the lyrics, put a timestamp in `[]` before each line, formatted as `[minutes:seconds]`. For example:
```
[1:23] Oh I love music
[0:06] Let it snow, let it snow, let it snow
```
Once you've timed each line, hit **Save**. From then on, while the song plays, the matching line will highlight in the media bar in sync with playback (assuming the timestamps are accurate). All lyrics are written into the same `.json` save file as everything else, so they'll still be there even if the app is closed or force-closed by accident.

<img width="2880" height="1800" alt="1001161326" src="https://github.com/user-attachments/assets/fd2192eb-a7cc-4d15-a0be-73bc9805bba3" />

# Installation

To run this app you need to install the following libraries. Some are "backups" used to read less common formats or to run on Android — if you want to save space, only install what you need, but installing everything is recommended for full compatibility. (`.apk` and `.exe` builds will be added to Releases once packaging is set up i dont know how to right now so probably not soon.)

### 1. Core Requirements (Must Install)
Required for the app to open and play standard audio formats (MP3, WAV, OGG, FLAC):
- **Pygame** — `pip install pygame` (rendering, input, and audio playback engine)
- **Mutagen** — `pip install mutagen` (reads song duration and extracts embedded cover art)

### 2. Backup Libraries (For Full Format Support)
Used as fallbacks to handle files like MP4, M4A, or AAC, and to decode some embedded JPEG cover art:
- **MoviePy** — `pip install moviepy` (extracts audio from video-container formats like MP4/M4A)
- **Pydub** — `pip install pydub` (alternative audio extraction if MoviePy fails)
- **Pillow** — `pip install pillow` (fallback JPEG decoder for embedded album art on platforms where Pygame's own decoder is incomplete)

### 3. Android Support (Mobile Only)
If you're going to use this on an Android device, you'll also need:
- **Pyjnius** (lets Python talk to native Android APIs — used for screen orientation, the system clipboard, and native MP4 playback)

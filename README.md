<div align="center">

# 🎵 SpotM-Fi

**A modern offline music player — your library, your device, no subscriptions.**

SpotM-Fi brings the look and feel of today's streaming services to your own music collection. Import your library, build playlists, sync lyrics, and listen without ever needing an internet connection.

[![Platform](https://img.shields.io/badge/platform-Windows%20%7C%20macOS%20%7C%20Android-blue)](#installation)
[![Language](https://img.shields.io/badge/language-Python-yellow)](#installation)
[![License](https://img.shields.io/badge/license-See%20License-lightgrey)](#license)

</div>

---

## ✨ Features at a Glance

| Category | What You Get |
|---|---|
| 🎧 **Playback** | Play, pause, skip, shuffle, repeat, seek |
| 📁 **Import** | Scan entire folders — all supported formats added automatically |
| 🖼️ **Artwork** | Auto-detected embedded art, custom covers, built-in online search |
| 🎤 **Lyrics** | Full editor with manual, clipboard, file import, and synchronized lyrics |
| 📊 **Statistics** | Play counts, skip counts, listening time, history |
| 📋 **Playlists** | Unlimited playlists with titles, descriptions, and custom artwork |
| 🌐 **Offline First** | Full playback with no internet required |
| 📱 **Cross-Platform** | Desktop (Windows/macOS) and Android, adaptive layout |

---

## 🎵 Supported Audio Formats

SpotM-Fi supports a wide range of formats out of the box, with even more available through optional libraries.

| Format | Support | Format | Support |
|--------|:-------:|--------|:-------:|
| MP3 | ✅ | AIFF / AIF | ✅ |
| WAV | ✅ | DSF | ✅ |
| FLAC | ✅ | DFF | ✅ |
| OGG | ✅ | MPEG Audio | ✅ |
| OPUS | ✅ | WMA | ⚠️ Platform Dependent |
| M4A | ✅ | MP4 Audio | ✅ |
| AAC | ✅ | ALAC | ✅ |

> Some formats require the optional libraries listed in [Installation](#installation).

---

## 🚀 Installation

SpotM-Fi is written in Python. Install the libraries below to get started. Pre-built `.exe` and `.apk` releases are coming to GitHub Releases once packaging is complete.

### 1 — Core Requirements *(Required)*

```bash
pip install pygame mutagen
```

Provides audio playback, rendering, input handling, metadata reading, and artwork extraction.

### 2 — Extended Audio Support *(Recommended)*

```bash
pip install moviepy pydub pillow
```

Adds support for MP4, M4A, AAC, ALAC, additional artwork formats, and fallback audio decoding. Recommended even if your library is mostly MP3.

### 3 — Android Support

```bash
pip install pyjnius
```

Enables native Android features including storage browsing, clipboard support, screen orientation, native media playback, and system integration. SpotM-Fi still runs without it, but some Android-specific features won't be available.

---

## 📖 How to Use

### Importing Music

1. Open **Search** in the sidebar.
2. Press **+ Add Folder**.
3. Browse to your music folder.
4. SpotM-Fi scans every supported audio file and imports it automatically.

> Your original music files are **never modified**. All SpotM-Fi data is stored separately.

### Navigation

The **sidebar** gives you quick access to:

- **Search** — find and import music
- **Your Library** — everything you've imported
- **Liked Songs** — tracks you've hearted
- **Playlists** — your custom collections
- **History Maker** — music history facts
- **Settings** — layout, grid, storage, preferences

The **media bar** at the bottom contains all playback controls including play/pause, previous/next, shuffle, repeat, 10-second skip, like, lyrics editor, and artwork changer.

Click or drag anywhere on the **progress bar** to seek within a track.

---

## 🖼️ Album Artwork

SpotM-Fi resolves artwork in this order:

1. Your custom uploaded artwork
2. Embedded artwork inside the audio file
3. Artwork downloaded via the built-in cover search
4. A clean placeholder image

Custom artwork is cached locally and loads instantly on future launches. Your original audio file is never touched.

**To change a song's artwork:** open the song from the media bar and press the picture frame icon. From there you can upload your own image, search online, or remove a custom cover.

**Best results:** use square images, 500×500 px or larger, in JPG or PNG format.

---

## 🎤 Lyrics

SpotM-Fi includes a full lyrics editor — no separate app needed.

Open it by pressing the **paper icon** in the media bar while a song is playing.

From the editor you can:
- Write or paste lyrics manually
- Import from a `.txt` file
- Search for lyrics online (with synchronized lyrics when available)
- Edit and save at any time

### Synchronized Lyrics

Add timestamps before each line to sync lyrics with playback:

```
[minutes:seconds:milliseconds]
```

**Example:**
```
[0:00:00] SpotM-Fi
[0:05:18] Playing my favourite music
[0:10:62] Offline forever
```

Once saved, the current lyric line is highlighted automatically as the song plays.

---

## 📊 Listening Statistics

SpotM-Fi quietly tracks playback data for every song in your library:

- **Play count** — how many times a track has played
- **Skip count** — how often you've skipped it
- **Listening time** — total time spent on each track
- **History** — recently played log

All stats are stored locally and never leave your device. Future versions will use this data to power smart playlists like Most Played, Forgotten Songs, Frequently Skipped, and Recommended Mixes.

---

## 🎲 Discovery Features

**Song of the Day** — Each day SpotM-Fi picks a random song from your library, a great way to rediscover music buried in your collection.

**Artist of the Day** — Highlights one artist from your library daily, giving everyone in your collection a moment in the spotlight.

**History Maker** — Browse interesting facts about music history directly inside the app: famous albums, legendary artists, historic performances, and important milestones.

---

## ⌨️ Keyboard Shortcuts *(Desktop)*

| Shortcut | Action |
|----------|--------|
| `Space` | Play / Pause |
| `Ctrl + V` | Paste lyrics |
| `Mouse Wheel` | Scroll library |
| `Left Click` | Select |
| `Right Click` | Context actions |

---

## ⚙️ Settings

| Option | Details |
|--------|---------|
| Layout | Switch between Desktop and Phone mode manually |
| Grid Size | 5–7 columns on desktop/tablet, 2–4 on phone |
| Imported Folders | View and manage your music sources |
| Storage | Manage cached artwork and local data |

---

## 💾 Data & Storage

Everything SpotM-Fi stores lives locally on your device:

- Playlists and descriptions
- Liked Songs
- Custom song and playlist artwork
- Lyrics
- Listening statistics
- User settings
- Recently played history
- Cached artwork (for faster loading)

Auto-save handles all of this continuously — there is no save button to press.

---

## 🔧 Troubleshooting

**Music doesn't import**
Make sure the folder contains supported audio files, the files aren't corrupted, and SpotM-Fi has permission to access that location.

**No album artwork**
Check whether the file has embedded art. If not, use the built-in Cover Search or assign your own image.

**Lyrics won't sync**
Double-check your timestamp format: `[minutes:seconds:milliseconds]` — for example `[1:23:45]`.

**Android features missing**
Ensure Pyjnius is installed, storage permissions are granted, and restart the app after changing permissions.

**Unsupported file format**
Install all optional libraries listed in the Installation section for the widest format compatibility.

---

## 🗺️ Roadmap

- Smart playlists driven by listening statistics (Most Played, Forgotten Songs, Recommended Mixes)
- Equalizer support
- Better metadata editing
- Improved search filters
- Additional Android improvements
- Official Windows installer, Android APK, Linux and macOS packages
- More themes and personalization options
- Additional music discovery features

---

## 🤝 Contributing

Contributions, bug reports, feature requests, and suggestions are all welcome. Open an issue or submit a pull request — every bit of feedback helps shape the project.

---

## 🙏 Credits

SpotM-Fi is built on these open-source libraries:

[Pygame](https://www.pygame.org) · [Mutagen](https://mutagen.readthedocs.io) · [MoviePy](https://zulko.github.io/moviepy/) · [Pydub](https://github.com/jiaaro/pydub) · [Pillow](https://pillow.readthedocs.io) · [Pyjnius](https://github.com/kivy/pyjnius)

Thanks also to the developers behind the APIs used for optional lyric and artwork searching.

---

## 📄 License

Provided as-is. Please do not redistribute modified versions without clearly stating your changes.

---

<div align="center">

**SpotM-Fi was built with one goal: a modern music player experience, completely under your control.**

*Whether you're on desktop or Android, your music stays yours.*

⭐ If you enjoy SpotM-Fi, consider starring the repository — it helps more than you'd think!

</div>

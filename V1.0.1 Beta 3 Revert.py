import pygame
import sys
import os
import tempfile
import time
import math
import random
import json

# --- WINDOW & SCALING CONFIGURATION ---
pygame.mixer.pre_init(44100, -16, 2, 2048)
pygame.init()
pygame.mixer.init()
pygame.font.init()

info = pygame.display.Info()
REAL_WIDTH, REAL_HEIGHT = info.current_w, info.current_h

try:
    DEVICE_REFRESH_RATE = info.refresh_rate
    if DEVICE_REFRESH_RATE == 0: 
        DEVICE_REFRESH_RATE = 60
except:
    DEVICE_REFRESH_RATE = 60

# --- PORTRAIT & SENSOR ORIENTATION ENGINE ---
# Enable device sensor auto-rotation on Android devices via jnius
try:
    from jnius import autoclass
    PythonActivity = autoclass('org.kivy.android.PythonActivity')
    ActivityInfo = autoclass('android.content.pm.ActivityInfo')
    # SCREEN_ORIENTATION_SENSOR = 4
    PythonActivity.mActivity.setRequestedOrientation(4)
except:
    pass

is_portrait = REAL_HEIGHT > REAL_WIDTH
WIDTH = 700 if is_portrait else 1100
HEIGHT = 1100 if is_portrait else 700

screen = pygame.display.set_mode((REAL_WIDTH, REAL_HEIGHT), pygame.FULLSCREEN | pygame.RESIZABLE)
virtual_surface = pygame.Surface((WIDTH, HEIGHT))
clock = pygame.time.Clock()

# FIXED: Safe compilation safeguard for platforms missing the pygame.scrap module entirely
HAS_DESKTOP_SCRAP = False
try:
    import pygame.scrap
    pygame.scrap.init()
    HAS_DESKTOP_SCRAP = True
except:
    pass

# --- COLOR PALETTE ---
COLOR_BLACK = (24, 24, 24)       
COLOR_DARK_GREY = (18, 18, 18)   
COLOR_LIGHT_GREY = (40, 40, 40)  
COLOR_SPOTIFY_GREEN = (30, 215, 96)
COLOR_WHITE = (255, 255, 255)
COLOR_TEXT_MUTED = (179, 179, 179)
COLOR_HOVER = (50, 50, 50)
COLOR_CARD_BG = (30, 30, 30)
COLOR_RED = (230, 50, 50)
COLOR_OVERLAY = (0, 0, 0, 200)

# --- FONTS ---
font_title = pygame.font.SysFont("Arial", 22, bold=True)
font_body = pygame.font.SysFont("Arial", 16, bold=True)
font_small = pygame.font.SysFont("Arial", 14)
font_huge = pygame.font.SysFont("Arial", 50, bold=True)

# --- APP STATE ---
current_page = "Search"  
current_track = {      
    "title": "Select a song",
    "artist": "No Artist",
    "duration": "0:00",
    "path": ""
}
is_playing = False     
is_shuffle = False  

green_toggled_tracks = set()

# --- AUDIO TRACKING STATE ---
track_duration = 0.0          
track_start_accumulator = 0.0 
TEMP_WAV_PATH = None          
current_backend = "pygame"    
music_loaded = False          
is_dragging_progress = False
drag_seek_target = 0.0

# Android Native Decoders Initialization
try:
    from jnius import autoclass
    MediaPlayer = autoclass('android.media.MediaPlayer')
    android_media_player = MediaPlayer()
    HAS_ANDROID_MEDIA = True
except:
    android_media_player = None
    HAS_ANDROID_MEDIA = False

# --- DUAL-PLATFORM HYBRID CLIPBOARD UTILITY ---
def get_clipboard_text():
    try:
        pasted_bytes = pygame.scrap.get(pygame.SCRAP_TEXT)
        if pasted_bytes:
            return pasted_bytes.decode('utf-8', errors='ignore').replace('\x00', '').replace('\r\n', '\n').replace('\r', '\n').replace('\xa0', ' ')
    except:
        pass
        
    if HAS_ANDROID_MEDIA:
        try:
            from jnius import autoclass
            PythonActivity = autoclass('org.kivy.android.PythonActivity')
            currentActivity = PythonActivity.mActivity
            Context = autoclass('android.content.Context')
            clipboard = currentActivity.getSystemService(Context.CLIPBOARD_SERVICE)
            if clipboard.hasPrimaryClip():
                clipData = clipboard.getPrimaryClip()
                if clipData.getItemCount() > 0:
                    item = clipData.getItemAt(0)
                    text_obj = item.getText()
                    if text_obj:
                        return text_obj.toString()
        except Exception as android_clip_err:
            print(f"Android Native Clipboard Error: {android_clip_err}")
            
    return ""

# --- DATA STORAGE ---
DATA_FILE = "SpotM-Fi.json"
sidebar_items = ["Search", "Your Library"] 
track_list = []
imported_tracks = []
liked_tracks = []        
saved_directories = []  

custom_playlists = {}  
liked_songs_custom_cover = {"image_path": None, "surface": None}
selected_custom_playlist_name = None
is_browsing_for_cover = False
browsing_cover_target = "create"

song_lyrics_database = {}  
show_lyrics_editor_view = False
lyrics_editor_cursor_timer = 0.0
lyrics_text_changed = False
lyrics_cursor_pos = 0

show_create_playlist_modal = False
playlist_input_text = ""
playlist_desc_text = ""
active_input_field = "name" 
show_add_to_playlist_modal = False
track_to_add_to_playlist = None
modal_playlist_cover_surface = None  
modal_playlist_cover_path = None

marquee_offset = 0.0
marquee_direction = 1

is_browsing_storage = False
search_input_active = False
search_query = ""
viewing_liked_playlist = False
viewing_settings_page = False  
playlist_is_playing = None  

is_dragging_grid = False
last_touch_y = 0
total_drag_dy = 0

music_grid_scroll_offset = 0.0  
target_music_scroll = 0.0
browser_scroll_offset = 0       
target_browser_scroll = 0.0     
settings_scroll_offset = 0
target_settings_scroll = 0.0
lyrics_scroll_offset = 0.0
target_lyrics_scroll = 0.0
max_music_scroll = 0
max_browser_scroll = 0
max_settings_scroll = 0
max_lyrics_scroll = 0

ROOT_PATH = "/storage/emulated/0" if os.path.exists("/storage/emulated/0") else "/sdcard"
current_browser_path = ROOT_PATH
browser_items = []  

search_message = "Tap '+ Add Folder' to open the built-in storage browser."

track_rects = []
sidebar_rects = []
browser_rects = []
settings_dir_rects = []
custom_playlist_rects = []
modal_playlist_rects = []

playlist_cover_rect = pygame.Rect(0, 0, 0, 0)
liked_songs_card_rect = pygame.Rect(260, 95, 160, 200)
search_box_rect = pygame.Rect(260, 80, 500, 40)
play_btn_rect = pygame.Rect(0, 0, 0, 0)
prev_btn_rect = pygame.Rect(0, 0, 0, 0)
next_btn_rect = pygame.Rect(0, 0, 0, 0)
minus_10_btn_rect = pygame.Rect(0, 0, 0, 0)
plus_10_btn_rect = pygame.Rect(0, 0, 0, 0)
shuffle_btn_rect = pygame.Rect(0, 0, 0, 0)
mediabar_add_btn_rect = pygame.Rect(0, 0, 0, 0)
mediabar_lyrics_btn_rect = pygame.Rect(0, 0, 0, 0)
star_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_play_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_random_btn_rect = pygame.Rect(0, 0, 0, 0) 
add_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
settings_btn_rect = pygame.Rect(0, 0, 0, 0)
create_playlist_btn_rect = pygame.Rect(390, 35, 40, 40)
select_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
cancel_browser_btn_rect = pygame.Rect(0, 0, 0, 0)
close_settings_btn_rect = pygame.Rect(0, 0, 0, 0)
progress_bar_rect = pygame.Rect(0, 0, 0, 0)

modal_close_rect = pygame.Rect(0, 0, 0, 0)
modal_save_rect = pygame.Rect(0, 0, 0, 0)
modal_input_rect = pygame.Rect(0, 0, 0, 0)
modal_desc_rect = pygame.Rect(0, 0, 0, 0)
modal_image_picker_rect = pygame.Rect(0, 0, 0, 0)

lyrics_close_rect = pygame.Rect(0, 0, 0, 0)
lyrics_save_rect = pygame.Rect(0, 0, 0, 0)
lyrics_textarea_rect = pygame.Rect(270, 145, 760, 420)

def save_app_data():
    data = {
        "saved_directories": saved_directories,
        "liked_tracks": liked_tracks,
        "liked_songs_custom_cover": {"image_path": liked_songs_custom_cover.get("image_path")},
        "custom_playlists": {},
        "song_lyrics_database": song_lyrics_database,
        "green_toggled_tracks": list(green_toggled_tracks)
    }
    
    for p_name, p_data in custom_playlists.items():
        data["custom_playlists"][p_name] = {
            "tracks": p_data["tracks"],
            "image_path": p_data["image_path"],
            "description": p_data["description"]
        }
        
    try:
        with open(DATA_FILE, "w") as f:
            json.dump(data, f, indent=4)
    except Exception as e:
        print(f"File Save Error: {e}")

def load_app_data():
    global saved_directories, liked_tracks, liked_songs_custom_cover
    global custom_playlists, song_lyrics_database, green_toggled_tracks
    
    if not os.path.exists(DATA_FILE):
        return
        
    try:
        with open(DATA_FILE, "r") as f:
            data = json.load(f)
            
        saved_directories = data.get("saved_directories", [])
        liked_tracks = data.get("liked_tracks", [])
        
        lsc = data.get("liked_songs_custom_cover", {})
        liked_songs_custom_cover["image_path"] = lsc.get("image_path")
        if liked_songs_custom_cover["image_path"] and os.path.exists(liked_songs_custom_cover["image_path"]):
            try:
                raw_img = pygame.image.load(liked_songs_custom_cover["image_path"])
                liked_songs_custom_cover["surface"] = pygame.transform.smoothscale(raw_img, (130, 110))
            except:
                pass
                
        song_lyrics_database = data.get("song_lyrics_database", {})
        green_toggled_tracks = set(data.get("green_toggled_tracks", []))
        
        loaded_playlists = data.get("custom_playlists", {})
        for p_name, p_data in loaded_playlists.items():
            surface = None
            if p_data.get("image_path") and os.path.exists(p_data["image_path"]):
                try:
                    raw_img = pygame.image.load(p_data["image_path"])
                    surface = pygame.transform.smoothscale(raw_img, (130, 110))
                except:
                    pass
            custom_playlists[p_name] = {
                "tracks": p_data.get("tracks", []),
                "image_path": p_data.get("image_path"),
                "description": p_data.get("description", ""),
                "surface": surface
            }
            
        rebuild_imported_tracks()
    except Exception as e:
        print(f"File Load Error: {e}")

def advance_track(backward=False):
    global current_track, is_playing, green_toggled_tracks
    if playlist_is_playing == "Liked Songs":
        playlist = liked_tracks
    elif playlist_is_playing in custom_playlists:
        playlist = custom_playlists[playlist_is_playing]["tracks"]
    else:
        playlist = imported_tracks
        
    if not playlist:
        return
    
    current_index = -1
    for i, track in enumerate(playlist):
        if track["path"] == current_track["path"]:
            current_index = i
            break
            
    if current_index != -1:
        if is_shuffle and len(playlist) > 1:
            next_index = current_index
            while next_index == current_index:
                next_index = random.randint(0, len(playlist) - 1)
        else:
            if backward:
                next_index = (current_index - 1) % len(playlist)
            else:
                next_index = (current_index + 1) % len(playlist)
                
        current_track = playlist[next_index]
        green_toggled_tracks.add(current_track["path"])
        is_playing = True
        load_and_play_track(current_track["path"])

def load_and_play_track(track_path):
    global track_duration, track_start_accumulator, TEMP_WAV_PATH, current_backend, music_loaded
    
    music_loaded = False
    try: 
        pygame.mixer.music.stop()
        pygame.mixer.music.unload() 
    except: pass
    
    if HAS_ANDROID_MEDIA and android_media_player:
        try: android_media_player.reset()
        except: pass

    if TEMP_WAV_PATH and os.path.exists(TEMP_WAV_PATH):
        try: os.remove(TEMP_WAV_PATH)
        except: pass
        TEMP_WAV_PATH = None

    track_start_accumulator = 0.0
    is_mp4 = track_path.lower().endswith(('.mp4', '.m4a', '.aac', '.alac', '.dsf', '.dff'))

    if is_mp4 and HAS_ANDROID_MEDIA and android_media_player:
        current_backend = "android"
        try:
            android_media_player.setDataSource(track_path)
            android_media_player.prepare()
            track_duration = android_media_player.getDuration() / 1000.0
            android_media_player.start()
            music_loaded = True
        except Exception as e:
            print(f"Android Native Decoder Error: {e}")
            music_loaded = False
    else:
        current_backend = "pygame"
        play_path = track_path
        duration = 0.0 

        if not is_mp4:
            try:
                snd_probe = pygame.mixer.Sound(track_path)
                duration = snd_probe.get_length()
            except:
                try:
                    from mutagen.mp3 import MP3
                    audio = MP3(track_path)
                    duration = audio.info.length
                except:
                    try:
                        from mutagen.oggvorbis import OggVorbis
                        audio = OggVorbis(track_path)
                        duration = audio.info.length
                    except:
                        try:
                            from mutagen.flac import FLAC
                            audio = FLAC(track_path)
                            duration = audio.info.length
                        except:
                            duration = 180.0
        else:
            try:
                from moviepy.editor import AudioFileClip
                clip = AudioFileClip(track_path)
                duration = clip.duration
                TEMP_WAV_PATH = os.path.join(tempfile.gettempdir(), "spotify_fi_temp.wav")
                clip.write_audiofile(TEMP_WAV_PATH, logger=None)
                clip.close()
                play_path = TEMP_WAV_PATH
            except:
                try:
                    from pydub import AudioSegment
                    sound = AudioSegment.from_file(track_path)
                    duration = len(sound) / 1000.0
                    TEMP_WAV_PATH = os.path.join(tempfile.gettempdir(), "spotify_fi_temp.wav")
                    sound.export(TEMP_WAV_PATH, format="wav")
                    play_path = TEMP_WAV_PATH
                except: pass

        track_duration = duration
        try:
            pygame.mixer.music.load(play_path)
            pygame.mixer.music.play(start=0.0)
            music_loaded = True
            current_track["_play_start_time"] = time.time()
            current_track["_has_started"] = False
        except Exception as e:
            print(f"Playback engine error: {e}")
            music_loaded = False

def update_browser_contents():
    global browser_items, search_message, browser_scroll_offset, target_browser_scroll
    browser_items = []
    browser_scroll_offset = 0
    target_browser_scroll = 0.0
    
    if current_browser_path != ROOT_PATH and current_browser_path != "/":
        browser_items.append({"name": "[.. Go Back to Previous Folder]", "is_dir": True, "path": os.path.dirname(current_browser_path)})
        
    try:
        for item in sorted(os.listdir(current_browser_path)):
            full_path = os.path.join(current_browser_path, item)
            is_dir = os.path.isdir(full_path)
            if is_browsing_for_cover and not is_dir and not item.lower().endswith(('.png', '.jpg', '.jpeg')):
                continue
            browser_items.append({"name": item, "is_dir": is_dir, "path": full_path})
    except Exception:
        search_message = "Access Denied: Restricted system folder or permission missing."

def rebuild_imported_tracks():
    global imported_tracks, search_message
    imported_tracks = []
    track_counter = 1
    new_songs_found = 0
    
    for directory in saved_directories:
        try:
            for file in os.listdir(directory):
                if file.lower().endswith(('.mp3', '.mp4', '.m4a', '.wav', '.ogg', '.flac', '.mpe', '.mpeg', '.aac', '.alac', '.dsf', '.dff')):
                    clean_title = os.path.splitext(file)[0]
                    
                    if len(clean_title) > 18:
                        display_title = clean_title[:15] + "..."
                    else:
                        display_title = clean_title
                        
                    track_data = {
                        "num": str(track_counter),
                        "title": display_title,
                        "raw_title": clean_title, 
                        "artist": "Local File",
                        "album": os.path.basename(directory) if os.path.basename(directory) else "Storage",
                        "duration": "Media",
                        "path": os.path.join(directory, file) 
                    }
                    imported_tracks.append(track_data)
                    track_counter += 1
                    new_songs_found += 1
        except Exception:
            continue
    if saved_directories:
        search_message = f"Scanned folders! Found {new_songs_found} media files in layout index."
    else:
        search_message = "Tap '+ Add Folder' to open the built-in storage browser."

def scan_confirmed_directory(target_dir):
    global saved_directories, music_grid_scroll_offset, target_music_scroll, is_browsing_storage, is_browsing_for_cover, selected_custom_playlist_name
    if is_browsing_for_cover:
        is_browsing_for_cover = False
        return
        
    if target_dir not in saved_directories:
        saved_directories.append(target_dir)
    music_grid_scroll_offset = 0.0
    target_music_scroll = 0.0
    rebuild_imported_tracks()
    is_browsing_storage = False  
    save_app_data() 
    
def get_virtual_mouse_pos():
    real_x, real_y = pygame.mouse.get_pos()
    scale_x = REAL_WIDTH / WIDTH
    scale_y = REAL_HEIGHT / HEIGHT
    
    virtual_x = int(real_x / scale_x)
    virtual_y = int(real_y / scale_y)
    return (virtual_x, virtual_y)


def draw_manual_thumbs_up(surface, x, y, w, h, color):
    pygame.draw.rect(surface, color, (x, y + h * 0.5, w * 0.22, h * 0.4), border_radius=max(1, int(w * 0.04)))
    pygame.draw.rect(surface, color, (x + w * 0.28, y + h * 0.35, w * 0.62, h * 0.55), border_radius=max(1, int(w * 0.06)))
    pygame.draw.rect(surface, color, (x + w * 0.28, y, w * 0.25, h * 0.45), border_radius=max(1, int(w * 0.06)))

def draw_piece_of_paper_icon(surface, rect, color):
    x, y, w, h = rect.x, rect.y, rect.width, rect.height
    px = x + 5
    py = y + 4
    pw = w - 10
    ph = h - 8
    
    pygame.draw.rect(surface, color, (px, py, pw, ph), width=2)
    pygame.draw.line(surface, color, (px + 4, py + 4), (px + pw - 4, py + 4), 2)
    pygame.draw.line(surface, color, (px + 4, py + 9), (px + pw - 4, py + 9), 2)
    pygame.draw.line(surface, color, (px + 4, py + 14), (px + pw - 4, py + 14), 2)

def draw_spotify_shuffle_icon(surface, rect, color):
    cx, cy = rect.centerx, rect.centery
    w, h = 16, 12
    x_left = cx - w // 2
    x_right = cx + w // 2
    y_top = cy - h // 2
    y_bottom = cy + h // 2
    
    pygame.draw.line(surface, color, (x_left, y_top), (cx - 2, y_top), 2)
    pygame.draw.line(surface, color, (cx - 2, y_top), (cx + 2, y_bottom), 2)
    pygame.draw.line(surface, color, (cx + 2, y_bottom), (x_right, y_bottom), 2)
    
    pygame.draw.line(surface, color, (x_left, y_bottom), (cx - 2, y_bottom), 2)
    pygame.draw.line(surface, color, (cx - 2, y_bottom), (cx + 2, y_top), 2)
    pygame.draw.line(surface, color, (cx + 2, y_top), (x_right, y_top), 2)
    
    pygame.draw.polygon(surface, color, [(x_right, y_top - 3), (x_right + 4, y_top), (x_right, y_top + 3)])
    pygame.draw.polygon(surface, color, [(x_right, y_bottom - 3), (x_right + 4, y_bottom), (x_right, y_bottom + 3)])

def draw_solid_cog_wheel(surface, x, y, w, h, color):
    cx, cy = x + w // 2, y + h // 2
    r_out = min(w, h) // 2
    
    pygame.draw.circle(surface, color, (cx, cy), int(r_out * 0.85))
    num_teeth = 8
    for i in range(num_teeth):
        angle = i * (2 * math.pi / num_teeth)
        tx = int(cx + r_out * math.cos(angle))
        ty = int(cy + r_out * math.sin(angle))
        pygame.draw.line(surface, color, (cx, cy), (tx, ty), width=int(r_out * 0.45))
        
    pygame.draw.circle(surface, COLOR_BLACK, (cx, cy), int(r_out * 0.25))

def draw_spotify_pencil(surface, cx, cy, color):
    pencil_surf = pygame.Surface((40, 40), pygame.SRCALPHA)
    pygame.draw.rect(pencil_surf, color, (12, 8, 8, 22))
    pygame.draw.polygon(pencil_surf, color, [(12, 30), (20, 30), (16, 36)])
    pygame.draw.rect(pencil_surf, COLOR_BLACK, (12, 5, 8, 3))
    
    rotated_surf = pygame.transform.rotate(pencil_surf, 45)
    new_rect = rotated_surf.get_rect(center=(cx, cy))
    surface.blit(rotated_surf, new_rect.topleft)

def draw_search_icon(surface, cx, cy, size, color):
    pygame.draw.circle(surface, color, (int(cx - size*0.1), int(cy - size*0.1)), int(size*0.3), width=2)
    pygame.draw.line(surface, color, (cx + size*0.1, cy + size*0.1), (cx + size*0.4, cy + size*0.4), width=3)

def draw_library_icon(surface, cx, cy, size, color):
    w = max(2, int(size * 0.15))
    h = int(size * 0.6)
    pygame.draw.rect(surface, color, (cx - size*0.4, cy - h//2, w, h), border_radius=1)
    pygame.draw.rect(surface, color, (cx - size*0.1, cy - h//2, w, h), border_radius=1)
    
    book_surf = pygame.Surface((w, h), pygame.SRCALPHA)
    pygame.draw.rect(book_surf, color, (0, 0, w, h), border_radius=1)
    rotated_book = pygame.transform.rotate(book_surf, -20)
    rect = rotated_book.get_rect(center=(cx + size*0.25, cy))
    surface.blit(rotated_book, rect.topleft)

def get_wrapped_lines(text, font, max_width):
    words = text.split(' ')
    lines = []
    current_line = ""
    
    for word in words:
        if font.size(word)[0] > max_width:
            if current_line:
                lines.append(current_line)
                current_line = ""
            for char in word:
                test_line = current_line + char
                if font.size(test_line)[0] <= max_width:
                    current_line = test_line
                else:
                    lines.append(current_line)
                    current_line = char
        else:
            test_line = current_line + " " + word if current_line else word
            if font.size(test_line)[0] <= max_width:
                current_line = test_line
            else:
                if current_line:
                    lines.append(current_line)
                current_line = word
                
    if current_line:
        lines.append(current_line)
    return lines

def draw_unified_cover_overlay(surface, rect, mouse_pos):
    if rect.collidepoint(mouse_pos):
        overlay_height = 32
        overlay_surf = pygame.Surface((rect.width, overlay_height), pygame.SRCALPHA)
        overlay_surf.fill((0, 0, 0, 180))
        
        hint_surf = font_small.render("Choose Cover Image", True, COLOR_WHITE)
        tx = (rect.width - hint_surf.get_width()) // 2
        ty = (overlay_height - hint_surf.get_height()) // 2
        overlay_surf.blit(hint_surf, (tx, ty))
        surface.blit(overlay_surf, (rect.x, rect.bottom - overlay_height))

def draw_sidebar():
    global sidebar_rects
    sidebar_rects = [] 
    
    content_bottom_margin = (130 if is_portrait else 90) if (current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal) else 0
    
    if not is_portrait:
        sidebar_rect = pygame.Rect(0, 0, 230, HEIGHT - content_bottom_margin)
        pygame.draw.rect(virtual_surface, COLOR_DARK_GREY, sidebar_rect)
        
        logo_text = font_title.render("SpotM-Fi", True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(logo_text, (20, 30))
        
        y_offset = 90
        mouse_pos = get_virtual_mouse_pos()
        
        for item in sidebar_items:
            item_rect = pygame.Rect(10, y_offset - 5, 210, 35)
            sidebar_rects.append((item_rect, item))
            
            is_hovered = item_rect.collidepoint(mouse_pos)
            is_clicked = is_hovered and pygame.mouse.get_pressed()[0]
            
            if is_clicked:
                pygame.draw.rect(virtual_surface, (60, 60, 60), item_rect, border_radius=5)
                text_color = COLOR_SPOTIFY_GREEN
            elif is_hovered or (current_page == item and not is_browsing_storage and not viewing_liked_playlist and not viewing_settings_page and not selected_custom_playlist_name and not show_create_playlist_modal and not show_add_to_playlist_modal and not show_lyrics_editor_view):
                pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=5)
                text_color = COLOR_WHITE
            else:
                text_color = COLOR_TEXT_MUTED
                
            text_surf = font_body.render(item, True, text_color)
            virtual_surface.blit(text_surf, (25, y_offset))
            y_offset += 40
    else:
        sidebar_height = 65
        sidebar_rect = pygame.Rect(0, HEIGHT - content_bottom_margin - sidebar_height, WIDTH, sidebar_height)
        pygame.draw.rect(virtual_surface, COLOR_DARK_GREY, sidebar_rect)
        
        mouse_pos = get_virtual_mouse_pos()
        item_width = WIDTH // len(sidebar_items)
        
        for i, item in enumerate(sidebar_items):
            item_rect = pygame.Rect(i * item_width, sidebar_rect.y, item_width, sidebar_height)
            sidebar_rects.append((item_rect, item))
            
            is_hovered = item_rect.collidepoint(mouse_pos)
            is_clicked = is_hovered and pygame.mouse.get_pressed()[0]
            
            if is_clicked:
                text_color = COLOR_SPOTIFY_GREEN
            elif is_hovered or (current_page == item and not is_browsing_storage and not viewing_liked_playlist and not viewing_settings_page and not selected_custom_playlist_name and not show_create_playlist_modal and not show_add_to_playlist_modal and not show_lyrics_editor_view):
                text_color = COLOR_WHITE
            else:
                text_color = COLOR_TEXT_MUTED
                
            cx = item_rect.centerx
            cy = item_rect.y + 22
            icon_size = 24
            
            if item == "Search":
                draw_search_icon(virtual_surface, cx, cy, icon_size, text_color)
            elif item == "Your Library":
                draw_library_icon(virtual_surface, cx, cy, icon_size, text_color)
                
            text_surf = font_small.render(item, True, text_color)
            tx = item_rect.x + (item_rect.width - text_surf.get_width()) // 2
            ty = item_rect.y + 40
            virtual_surface.blit(text_surf, (tx, ty))

def draw_main_content():
    global track_rects, add_folder_btn_rect, settings_btn_rect, create_playlist_btn_rect, browser_rects, settings_dir_rects, custom_playlist_rects, select_folder_btn_rect, cancel_browser_btn_rect, close_settings_btn_rect, liked_songs_card_rect, playlist_play_btn_rect, playlist_random_btn_rect, playlist_cover_rect, max_music_scroll, max_browser_scroll, max_settings_scroll, marquee_offset, marquee_direction
    track_rects = []
    browser_rects = []
    settings_dir_rects = []
    custom_playlist_rects = []
    
    content_bottom_margin = (130 if is_portrait else 90) if (current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal) else 0
    portrait_sidebar_h = 65 if is_portrait else 0
    
    main_x = 0 if is_portrait else 230
    main_y = 0
    main_w = WIDTH - main_x
    main_h = HEIGHT - content_bottom_margin - portrait_sidebar_h
    content_pad_x = main_x + 30
    
    main_rect = pygame.Rect(main_x, main_y, main_w, main_h)
    pygame.draw.rect(virtual_surface, COLOR_BLACK, main_rect)
    mouse_pos = get_virtual_mouse_pos()

    if show_add_to_playlist_modal or show_lyrics_editor_view:
        return

    # --- DETAILED PLAYLIST VIEWS ---
    if (viewing_liked_playlist or selected_custom_playlist_name) and current_page == "Your Library" and not is_browsing_for_cover:
        is_custom = selected_custom_playlist_name is not None
        active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if is_custom else liked_tracks
        p_title_text = selected_custom_playlist_name if is_custom else "Liked Songs"
        
        header_rect = pygame.Rect(main_x, 0, main_w, 200)
        pygame.draw.rect(virtual_surface, COLOR_HOVER, header_rect)
        
        playlist_cover_rect = pygame.Rect(content_pad_x, 30, 140, 140)
        
        if is_custom and custom_playlists[selected_custom_playlist_name]["surface"]:
            disp_surf = pygame.transform.smoothscale(custom_playlists[selected_custom_playlist_name]["surface"], (140, 140))
            virtual_surface.blit(disp_surf, (content_pad_x, 30))
        elif not is_custom and liked_songs_custom_cover["surface"]:
            disp_surf = pygame.transform.smoothscale(liked_songs_custom_cover["surface"], (140, 140))
            virtual_surface.blit(disp_surf, (content_pad_x, 30))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, playlist_cover_rect)
            if not is_custom:
                draw_manual_thumbs_up(virtual_surface, content_pad_x + 45, 75, 50, 50, COLOR_BLACK)
            else:
                draw_spotify_pencil(virtual_surface, content_pad_x + 70, 100, COLOR_BLACK)
                
        draw_unified_cover_overlay(virtual_surface, playlist_cover_rect, mouse_pos)
        
        type_lbl = font_small.render("CUSTOM PLAYLIST" if is_custom else "PUBLIC PLAYLIST", True, COLOR_WHITE)
        playlist_title = font_huge.render(p_title_text, True, COLOR_WHITE)
        
        virtual_surface.blit(type_lbl, (content_pad_x + 160, 45))
        virtual_surface.blit(playlist_title, (content_pad_x + 160, 70))

        if is_custom:
            desc_str = custom_playlists[selected_custom_playlist_name].get("description", "")
            base_meta_str = f" • {len(active_tracks)} songs"
            
            if desc_str:
                desc_w = font_body.size(desc_str)[0]
                meta_w = font_body.size(base_meta_str)[0]
                max_allowed_w = main_w - 210 - meta_w
                
                if desc_w > max_allowed_w and max_allowed_w > 0:
                    max_scroll_range = desc_w - max_allowed_w
                    marquee_offset += marquee_direction * (40.0 * (clock.get_time() / 1000.0))
                    
                    if marquee_offset >= max_scroll_range + 20:
                        marquee_offset = max_scroll_range + 20
                        marquee_direction = -1
                    elif marquee_offset <= -20:
                        marquee_offset = -20
                        marquee_direction = 1
                    
                    marquee_surf = pygame.Surface((max_allowed_w, 24), pygame.SRCALPHA)
                    desc_raw_surf = font_body.render(desc_str, True, COLOR_WHITE)
                    marquee_surf.blit(desc_raw_surf, (-int(marquee_offset), 0))
                    virtual_surface.blit(marquee_surf, (content_pad_x + 160, 140))
                    
                    meta_lbl = font_body.render(base_meta_str, True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(meta_lbl, (content_pad_x + 160 + max_allowed_w, 140))
                else:
                    info_lbl = font_body.render(f"{desc_str}{base_meta_str}", True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(info_lbl, (content_pad_x + 160, 140))
            else:
                info_lbl = font_body.render(f"Local Account{base_meta_str}", True, COLOR_TEXT_MUTED)
                virtual_surface.blit(info_lbl, (content_pad_x + 160, 140))
        else:
            info_lbl = font_body.render(f"Local Account • {len(active_tracks)} songs", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(info_lbl, (content_pad_x + 160, 140))
        
        playlist_play_btn_rect = pygame.Rect(content_pad_x, 215, 50, 50)
        is_p_hovered = playlist_play_btn_rect.collidepoint(mouse_pos)
        is_p_clicked = is_p_hovered and pygame.mouse.get_pressed()[0]
        
        if is_p_clicked:
            pygame.draw.circle(virtual_surface, (20, 150, 65), (content_pad_x + 25, 240), 23)
        elif is_p_hovered:
            pygame.draw.circle(virtual_surface, (40, 230, 110), (content_pad_x + 25, 240), 26)
        else:
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (content_pad_x + 25, 240), 25)
            
        if not (is_playing and playlist_is_playing == p_title_text):
            pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(content_pad_x + 20, 230), (content_pad_x + 20, 250), (content_pad_x + 35, 240)])
        else:
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (content_pad_x + 19, 232, 4, 16))
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (content_pad_x + 27, 232, 4, 16))

        playlist_random_btn_rect = pygame.Rect(content_pad_x + 65, 222, 36, 36)
        is_pr_hovered = playlist_random_btn_rect.collidepoint(mouse_pos)
        if is_pr_hovered:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, playlist_random_btn_rect.center, 18)
            
        if is_shuffle:
            shuffle_icon_color = COLOR_SPOTIFY_GREEN
        else:
            shuffle_icon_color = COLOR_WHITE if is_pr_hovered else COLOR_TEXT_MUTED
            
        draw_spotify_shuffle_icon(virtual_surface, playlist_random_btn_rect, shuffle_icon_color)
        if is_shuffle:
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (playlist_random_btn_rect.centerx, playlist_random_btn_rect.centery + 12), 2)
            
        hash_lbl = font_small.render("#  TITLE", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(hash_lbl, (content_pad_x + 10, 285))
        
        if not is_portrait:
            album_lbl = font_small.render("ALBUM", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(album_lbl, (content_pad_x + 390, 285))
            
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 305), (main_x + main_w - 40, 305), 1)
        
        total_content_height = len(active_tracks) * 50
        max_music_scroll = max(0, total_content_height - (main_h - 315) + 50)
        
        clip_rect = pygame.Rect(main_x, 315, main_w, main_h - 315)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 315 - int(music_grid_scroll_offset)
        for index, track in enumerate(active_tracks):
            row_rect = pygame.Rect(main_x + 20, y_offset, main_w - 50, 45)
            if row_rect.colliderect(clip_rect):
                track_rects.append((row_rect, track))
                
                is_row_hovered = row_rect.collidepoint(mouse_pos)
                is_row_clicked = is_row_hovered and pygame.mouse.get_pressed()[0]
                
                if is_row_clicked:
                    pygame.draw.rect(virtual_surface, (60, 60, 60), row_rect, border_radius=6)
                elif track["path"] in green_toggled_tracks and track["title"] == current_track["title"]:
                    pygame.draw.rect(virtual_surface, (40, 60, 45), row_rect, border_radius=6)
                elif is_row_hovered:
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, row_rect, border_radius=6)
                
                if track["title"] == current_track["title"]:
                    title_color = COLOR_SPOTIFY_GREEN
                else:
                    title_color = COLOR_WHITE
                
                num_surf = font_body.render(str(index + 1), True, COLOR_TEXT_MUTED)
                title_surf = font_body.render(track["title"], True, title_color)
                artist_surf = font_small.render(track["artist"], True, COLOR_TEXT_MUTED)
                
                virtual_surface.blit(num_surf, (main_x + 40, y_offset + 12))
                virtual_surface.blit(title_surf, (main_x + 80, y_offset + 4))
                virtual_surface.blit(artist_surf, (main_x + 80, y_offset + 24))
                
                if not is_portrait:
                    album_surf = font_body.render(track["album"], True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(album_surf, (main_x + 420, y_offset + 12))
                
            y_offset += 50
        virtual_surface.set_clip(None)

    # --- STORAGE BROWSER ---
    elif (is_browsing_storage or is_browsing_for_cover) and current_page in ["Search", "Your Library"]:
        title_string = "Import custom cover picture (.png, .jpg)" if is_browsing_for_cover else "Device Storage Explorer"
        browser_title = font_title.render(title_string, True, COLOR_WHITE)
        virtual_surface.blit(browser_title, (content_pad_x, 40))
        
        path_lbl = font_small.render(f"Path: {current_browser_path}", True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(path_lbl, (content_pad_x, 75))
        
        select_folder_btn_rect = pygame.Rect(main_x + main_w - 270, 35, 160, 35)
        cancel_browser_btn_rect = pygame.Rect(main_x + main_w - 100, 35, 90, 35)
        
        sf_hovered = select_folder_btn_rect.collidepoint(mouse_pos)
        sf_clicked = sf_hovered and pygame.mouse.get_pressed()[0]
        if sf_clicked:
            sf_color = (20, 150, 65)
        else:
            sf_color = COLOR_SPOTIFY_GREEN if sf_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, sf_color, select_folder_btn_rect, border_radius=15)
        
        sf_text = "✓ Confirm File" if is_browsing_for_cover else "✓ Select Current"
        sf_lbl = font_small.render(sf_text, True, COLOR_WHITE if sf_color == COLOR_LIGHT_GREY else COLOR_BLACK)
        virtual_surface.blit(sf_lbl, (select_folder_btn_rect.x + 25, 44))
        
        cc_hovered = cancel_browser_btn_rect.collidepoint(mouse_pos)
        cc_clicked = cc_hovered and pygame.mouse.get_pressed()[0]
        if cc_clicked:
            cc_color = (30, 30, 30)
        else:
            cc_color = COLOR_HOVER if cc_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, cc_color, cancel_browser_btn_rect, border_radius=15)
        cc_lbl = font_small.render("Cancel", True, COLOR_WHITE)
        virtual_surface.blit(cc_lbl, (cancel_browser_btn_rect.x + 20, 44))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)
        
        total_content_height = len(browser_items) * 42
        max_browser_scroll = max(0, total_content_height - (main_h - 130) + 30)
        
        clip_rect = pygame.Rect(main_x, 130, main_w, main_h - 130)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 130 - int(browser_scroll_offset)
        for item in browser_items:
            item_row_rect = pygame.Rect(main_x + 20, y_offset - 4, main_w - 50, 35)
            if item_row_rect.colliderect(clip_rect):
                browser_rects.append((item_row_rect, item))
                
                is_b_hovered = item_row_rect.collidepoint(mouse_pos)
                is_b_clicked = is_b_hovered and pygame.mouse.get_pressed()[0]
                
                if is_b_clicked:
                    pygame.draw.rect(virtual_surface, (60, 60, 60), item_row_rect, border_radius=5)
                elif is_b_hovered:
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, item_row_rect, border_radius=5)
                    
                if item["is_dir"]:
                    prefix = "[FOLDER] "
                    display_color = COLOR_TEXT_MUTED
                else:
                    prefix = "[IMAGE] "
                    display_color = COLOR_SPOTIFY_GREEN
                
                item_surf = font_body.render(f"{prefix}{item['name']}", True, display_color)
                virtual_surface.blit(item_surf, (content_pad_x, y_offset))
            y_offset += 42
        virtual_surface.set_clip(None)

    # --- DEDICATED SETTINGS PAGE VIEW ---
    elif viewing_settings_page and current_page == "Search":
        settings_title = font_title.render("Imported Music Directories", True, COLOR_WHITE)
        virtual_surface.blit(settings_title, (content_pad_x, 40))
        
        if not is_portrait:
            close_settings_btn_rect = pygame.Rect(main_x + main_w - 250, 35, 90, 35)
        else:
            close_settings_btn_rect = pygame.Rect(main_x + main_w - 110, 35, 90, 35)
            
        cs_hovered = close_settings_btn_rect.collidepoint(mouse_pos)
        cs_clicked = cs_hovered and pygame.mouse.get_pressed()[0]
        if cs_clicked:
            cs_color = (30, 30, 30)
        else:
            cs_color = COLOR_HOVER if cs_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, cs_color, close_settings_btn_rect, border_radius=15)
        cs_lbl = font_small.render("Back", True, COLOR_WHITE)
        virtual_surface.blit(cs_lbl, (close_settings_btn_rect.x + 26, 44))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)
        
        total_content_height = len(saved_directories) * 50
        max_settings_scroll = max(0, total_content_height - (main_h - 130) + 30)
        
        clip_rect = pygame.Rect(main_x, 130, main_w, main_h - 130)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 130 - int(settings_scroll_offset)
        for d_path in saved_directories:
            row_item_rect = pygame.Rect(main_x + 20, y_offset - 4, main_w - 50, 42)
            if row_item_rect.colliderect(clip_rect):
                settings_dir_rects.append((row_item_rect, d_path))
                
                is_row_h = row_item_rect.collidepoint(mouse_pos)
                row_bg = COLOR_RED if is_row_h else COLOR_LIGHT_GREY
                pygame.draw.rect(virtual_surface, row_bg, row_item_rect, border_radius=6)
                
                lbl_path = font_body.render(f"  [FOLDER]  {d_path}", True, COLOR_WHITE)
                lbl_del = font_body.render("Delete [x]" if is_portrait else "Delete and Clear Music  [x] ", True, COLOR_WHITE if is_row_h else COLOR_TEXT_MUTED)
                
                virtual_surface.blit(lbl_path, (main_x + 35, y_offset + 6))
                virtual_surface.blit(lbl_del, (main_x + main_w - (120 if is_portrait else 250), y_offset + 6))
            y_offset += 50
        virtual_surface.set_clip(None)

    # --- SEARCH PAGE ---
    elif current_page == "Search":
        search_title = font_title.render("Search Results", True, COLOR_WHITE)
        virtual_surface.blit(search_title, (content_pad_x, 40))
        
        if not is_portrait:
            add_folder_btn_rect = pygame.Rect(content_pad_x + 520, 80, 150, 40)
        else:
            add_folder_btn_rect = pygame.Rect(main_x + main_w - 220, 80, 150, 40)
            
        is_af_hovered = add_folder_btn_rect.collidepoint(mouse_pos)
        is_af_clicked = is_af_hovered and pygame.mouse.get_pressed()[0]
        
        if is_af_clicked:
            pygame.draw.rect(virtual_surface, (20, 150, 65), add_folder_btn_rect, border_radius=20)
            btn_color = COLOR_WHITE
        elif is_af_hovered:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, add_folder_btn_rect, border_radius=20)
            btn_color = COLOR_BLACK
        else:
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, add_folder_btn_rect, border_radius=20)
            btn_color = COLOR_WHITE
            
        btn_txt = font_small.render("+ Add Folder", True, btn_color)
        virtual_surface.blit(btn_txt, (add_folder_btn_rect.x + 38, 92))

        if saved_directories:
            if not is_portrait:
                settings_btn_rect = pygame.Rect(content_pad_x + 680, 80, 40, 40)
            else:
                settings_btn_rect = pygame.Rect(main_x + main_w - 55, 80, 40, 40)
                
            is_st_hovered = settings_btn_rect.collidepoint(mouse_pos)
            is_st_clicked = is_st_hovered and pygame.mouse.get_pressed()[0]
            
            if is_st_clicked:
                box_bg_color = (20, 150, 65)
                st_color = COLOR_WHITE
            elif is_st_hovered:
                box_bg_color = COLOR_SPOTIFY_GREEN
                st_color = COLOR_BLACK
            else:
                box_bg_color = COLOR_LIGHT_GREY
                st_color = COLOR_WHITE
                
            pygame.draw.rect(virtual_surface, box_bg_color, settings_btn_rect, border_radius=20)
            draw_solid_cog_wheel(virtual_surface, settings_btn_rect.x + 10, settings_btn_rect.y + 10, 20, 20, st_color)

        search_box_rect = pygame.Rect(content_pad_x, 80, 500 if not is_portrait else main_w - 280, 40)
        pygame.draw.rect(virtual_surface, COLOR_WHITE, search_box_rect, border_radius=20)
        if search_input_active and not show_create_playlist_modal:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, search_box_rect, width=2, border_radius=20)
            
        if search_query != "":
            search_text = font_small.render(f"  {search_query}", True, COLOR_BLACK)
        else:
            search_text = font_small.render(f"  {search_message}", True, COLOR_LIGHT_GREY)
        virtual_surface.blit(search_text, (content_pad_x + 15, 92))

        filtered_tracks = []
        cleaned_query = search_query.strip().lower()
        for track in imported_tracks:
            if cleaned_query == "" or cleaned_query in track["raw_title"].lower() or cleaned_query in track["album"].lower():
                filtered_tracks.append(track)

        if not imported_tracks:
            empty_surf = font_body.render("No local music loaded. Tap '+ Add Folder' above to explore your storage!", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_surf, (content_pad_x, 160))
        elif not filtered_tracks:
            no_match_surf = font_body.render(f"No results match your search query for '{search_query}'.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(no_match_surf, (content_pad_x, 160))
        else:
            start_x = content_pad_x
            start_y = 150
            card_width = 140
            card_height = 140
            gap_x = 14  
            gap_y = 55  
            
            cols = (main_w - 20) // (card_width + gap_x)
            if cols < 1: cols = 1
            rows = (len(filtered_tracks) + cols - 1) // cols if cols > 0 else 0
            total_content_height = rows * (card_height + gap_y)
            max_music_scroll = max(0, total_content_height - (main_h - 140) + 50)
            
            clip_rect = pygame.Rect(main_x, 140, main_w, main_h - 140)
            virtual_surface.set_clip(clip_rect)
            
            for index, track in enumerate(filtered_tracks):
                col = index % cols
                row = index // cols
                
                box_x = start_x + (col * (card_width + gap_x))
                box_y = start_y + (row * (card_height + gap_y)) - int(music_grid_scroll_offset)
                
                card_rect = pygame.Rect(box_x, box_y, card_width, card_height + 40)
                
                if card_rect.colliderect(clip_rect):
                    track_rects.append((card_rect, track))
                    
                    is_card_hovered = card_rect.collidepoint(mouse_pos)
                    is_card_clicked = is_card_hovered and pygame.mouse.get_pressed()[0]
                    
                    if is_card_clicked:
                        pygame.draw.rect(virtual_surface, (45, 45, 45), card_rect, border_radius=8)
                    elif track["path"] in green_toggled_tracks and track["title"] == current_track["title"]:
                        pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, card_rect, width=2, border_radius=8)
                    elif is_card_hovered:
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, card_rect, border_radius=8)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_CARD_BG, card_rect, border_radius=8)
                    
                    cover_rect = pygame.Rect(box_x + 12, box_y + 12, card_width - 24, card_height - 24)
                    pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, border_radius=6)
                    
                    if track["title"] == current_track["title"]:
                        title_color = COLOR_SPOTIFY_GREEN
                        sub_color = COLOR_TEXT_MUTED
                    else:
                        title_color = COLOR_WHITE
                        sub_color = COLOR_TEXT_MUTED
                        
                    title_surf = font_small.render(track["title"], True, title_color)
                    virtual_surface.blit(title_surf, (box_x + 12, box_y + card_height - 4))
                    
                    sub_surf = font_small.render(track["album"], True, sub_color)
                    virtual_surface.blit(sub_surf, (box_x + 12, box_y + card_height + 14))
            virtual_surface.set_clip(None)

    # --- YOUR LIBRARY GRID VIEW ---
    elif current_page == "Your Library":
        lib_title = font_title.render("Your Library", True, COLOR_WHITE)
        virtual_surface.blit(lib_title, (content_pad_x, 40))
        
        create_playlist_btn_rect = pygame.Rect(content_pad_x + 130, 35, 40, 40)
        is_cp_hovered = create_playlist_btn_rect.collidepoint(mouse_pos)
        is_cp_clicked = is_cp_hovered and pygame.mouse.get_pressed()[0]
        
        if is_cp_clicked:
            cp_box_color = (20, 150, 65)
            cp_text_color = COLOR_WHITE
        elif is_cp_hovered:
            cp_box_color = COLOR_SPOTIFY_GREEN
            cp_text_color = COLOR_BLACK
        else:
            cp_box_color = COLOR_LIGHT_GREY
            cp_text_color = COLOR_WHITE
            
        pygame.draw.rect(virtual_surface, cp_box_color, create_playlist_btn_rect, border_radius=20)
        cp_plus_surf = font_body.render("+", True, cp_text_color)
        
        plus_x = create_playlist_btn_rect.x + (create_playlist_btn_rect.width - cp_plus_surf.get_width()) // 2
        plus_y = create_playlist_btn_rect.y + (create_playlist_btn_rect.height - cp_plus_surf.get_height()) // 2
        virtual_surface.blit(cp_plus_surf, (plus_x, plus_y))
        
        liked_songs_card_rect = pygame.Rect(content_pad_x, 95, 160, 200)
        is_lib_hovered = liked_songs_card_rect.collidepoint(mouse_pos)
        is_lib_clicked = is_lib_hovered and pygame.mouse.get_pressed()[0]
        
        if is_lib_clicked:
            pygame.draw.rect(virtual_surface, (45, 45, 45), liked_songs_card_rect, border_radius=8)
        elif is_lib_hovered:
            pygame.draw.rect(virtual_surface, COLOR_HOVER, liked_songs_card_rect, border_radius=8)
        else:
            pygame.draw.rect(virtual_surface, COLOR_CARD_BG, liked_songs_card_rect, border_radius=8)
            
        if liked_songs_custom_cover["surface"]:
            disp_thumb = pygame.transform.smoothscale(liked_songs_custom_cover["surface"], (130, 110))
            virtual_surface.blit(disp_thumb, (content_pad_x + 15, 110))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, (content_pad_x + 15, 110, 130, 110), border_radius=4)
            draw_manual_thumbs_up(virtual_surface, content_pad_x + 55, 140, 50, 50, COLOR_BLACK)
        
        card_txt1 = font_body.render("Liked Songs", True, COLOR_WHITE)
        card_txt2 = font_small.render(f"Playlist • {len(liked_tracks)} songs", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(card_txt1, (content_pad_x + 15, 230))
        virtual_surface.blit(card_txt2, (content_pad_x + 15, 255))

        start_x = content_pad_x
        start_y = 95
        card_w, card_h = 160, 200
        gap_x, gap_y = 20, 20
        columns_count = (main_w - 20) // (card_w + gap_x)
        if columns_count < 1: columns_count = 1
        
        for idx, p_name in enumerate(list(custom_playlists.keys())):
            layout_index = idx + 1
            col = layout_index % columns_count
            row = layout_index // columns_count
            
            box_x = start_x + (col * (card_w + gap_x))
            box_y = start_y + (row * (card_h + gap_y)) - int(music_grid_scroll_offset)
            
            c_rect = pygame.Rect(box_x, box_y, card_w, card_h)
            custom_playlist_rects.append((c_rect, p_name))
            
            is_c_hover = c_rect.collidepoint(mouse_pos)
            if is_c_hover and pygame.mouse.get_pressed()[0]:
                pygame.draw.rect(virtual_surface, (45, 45, 45), c_rect, border_radius=8)
            elif is_c_hover:
                pygame.draw.rect(virtual_surface, COLOR_HOVER, c_rect, border_radius=8)
            else:
                pygame.draw.rect(virtual_surface, COLOR_CARD_BG, c_rect, border_radius=8)
                
            cover_frame = pygame.Rect(box_x + 15, box_y + 15, 130, 110)
            if custom_playlists[p_name]["surface"]:
                disp_thumb = pygame.transform.smoothscale(custom_playlists[p_name]["surface"], (130, 110))
                virtual_surface.blit(disp_thumb, (box_x + 15, box_y + 15))
            else:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, cover_frame, border_radius=4)
                draw_spotify_pencil(virtual_surface, box_x + 80, box_y + 70, COLOR_BLACK)
                
            name_lbl = font_body.render(p_name if len(p_name) <= 14 else p_name[:12] + "...", True, COLOR_WHITE)
            count_lbl = font_small.render(f"Playlist • {len(custom_playlists[p_name]['tracks'])} tracks", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(name_lbl, (box_x + 15, box_y + 135))
            virtual_surface.blit(count_lbl, (box_x + 15, box_y + 160))

# --- MODAL RENDERING ENGINE ---
def draw_modals():
    global modal_close_rect, modal_save_rect, modal_input_rect, modal_desc_rect, modal_playlist_rects, modal_image_picker_rect, lyrics_close_rect, lyrics_save_rect, lyrics_textarea_rect, max_music_scroll, lyrics_editor_cursor_timer, max_lyrics_scroll, target_lyrics_scroll, lyrics_text_changed
    mouse_pos = get_virtual_mouse_pos()
    
    portrait_sidebar_h = 65 if is_portrait else 0
    main_x = 0 if is_portrait else 230
    main_w = WIDTH - main_x
    content_bottom_margin = (130 if is_portrait else 90) if (current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal) else 0
    main_h = HEIGHT - content_bottom_margin - portrait_sidebar_h
    content_pad_x = main_x + 30
    
    if show_lyrics_editor_view:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT))
        
        track_ref = current_track.get("path", "")
        current_lyrics_str = song_lyrics_database.get(track_ref, "")
        
        header_lbl = font_huge.render("Edit Song Lyrics", True, COLOR_SPOTIFY_GREEN)
        track_lbl = font_body.render(f"Track: {current_track['title']} • {current_track['artist']}", True, COLOR_WHITE)
        virtual_surface.blit(header_lbl, (main_x + 40, 45))
        virtual_surface.blit(track_lbl, (main_x + 40, 105))
        
        lyrics_box_h = HEIGHT - 250 if is_portrait else 420
        lyrics_textarea_rect = pygame.Rect(main_x + 40, 145, main_w - 80, lyrics_box_h)
        pygame.draw.rect(virtual_surface, COLOR_CARD_BG, lyrics_textarea_rect, border_radius=8)
        
        if search_input_active and active_input_field == "lyrics":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, lyrics_textarea_rect, width=2, border_radius=8)
            
        if current_lyrics_str or current_lyrics_str == "":
            elapsed_sec = 0.0
            if track_duration > 0 and music_loaded:
                if current_backend == "android" and android_media_player:
                    try: elapsed_sec = android_media_player.getCurrentPosition() / 1000.0
                    except: elapsed_sec = 0.0
                else:
                    mix_pos = pygame.mixer.music.get_pos()
                    if mix_pos == -1:
                        elapsed_sec = track_duration if current_track.get("_has_started", False) else track_start_accumulator
                    else:
                        elapsed_sec = track_start_accumulator + (mix_pos / 1000.0)
                elapsed_sec = min(track_duration, elapsed_sec)

            lines = current_lyrics_str.split('\n')
            active_line_idx = -1
            best_time = -1
            for i, line in enumerate(lines):
                line_stripped = line.strip()
                if line_stripped.startswith('[') and ']' in line_stripped:
                    try:
                        time_part = line_stripped.split(']', 1)[0][1:].strip()
                        if ':' in time_part:
                            t_parts = time_part.split(':')
                            lyric_time = float(t_parts[0]) * 60 + float(t_parts[1])
                            if lyric_time <= elapsed_sec and lyric_time > best_time:
                                best_time = lyric_time
                                active_line_idx = i
                    except:
                        pass

            total_lyrics_height = 0
            for line in lines:
                wrapped_sublines = get_wrapped_lines(line, font_small, lyrics_textarea_rect.width - 40)
                if wrapped_sublines:
                    total_lyrics_height += len(wrapped_sublines) * 20
                if not line:
                    total_lyrics_height += 12
                    
            if total_lyrics_height > lyrics_box_h:
                max_lyrics_scroll = max(0, total_lyrics_height - (lyrics_textarea_rect.height - 30))
            else:
                max_lyrics_scroll = 0

            if lyrics_text_changed:
                target_lyrics_scroll = max_lyrics_scroll
                lyrics_text_changed = False

            virtual_surface.set_clip(lyrics_textarea_rect)

            y_pos = lyrics_textarea_rect.y + 15 - int(lyrics_scroll_offset)
            
            temp_idx = 0
            target_line_idx = 0
            target_char_offset = 0
            for idx, l in enumerate(lines):
                if temp_idx <= lyrics_cursor_pos <= temp_idx + len(l):
                    target_line_idx = idx
                    target_char_offset = lyrics_cursor_pos - temp_idx
                    break
                temp_idx += len(l) + 1

            cursor_x = lyrics_textarea_rect.x + 15
            cursor_y = y_pos
            cursor_drawn_for_line = False
            
            for i, line in enumerate(lines):
                wrapped_sublines = get_wrapped_lines(line, font_small, lyrics_textarea_rect.width - 40)
                line_color = COLOR_SPOTIFY_GREEN if i == active_line_idx else COLOR_WHITE
                
                if not line:
                    if i == target_line_idx:
                        cursor_x = lyrics_textarea_rect.x + 15
                        cursor_y = y_pos
                    y_pos += 12
                else:
                    accumulated_chars = 0
                    for sub_idx, sl in enumerate(wrapped_sublines):
                        line_surf = font_small.render(sl, True, line_color)
                        virtual_surface.blit(line_surf, (lyrics_textarea_rect.x + 15, y_pos))
                        
                        if i == target_line_idx and not cursor_drawn_for_line:
                            next_accumulated = accumulated_chars + len(sl)
                            if accumulated_chars <= target_char_offset <= next_accumulated:
                                rem_offset = target_char_offset - accumulated_chars
                                cursor_x = lyrics_textarea_rect.x + 15 + font_small.size(sl[:rem_offset])[0]
                                cursor_y = y_pos
                                cursor_drawn_for_line = True
                            elif sub_idx == len(wrapped_sublines) - 1:
                                cursor_x = lyrics_textarea_rect.x + 15 + font_small.size(sl)[0]
                                cursor_y = y_pos
                                cursor_drawn_for_line = True
                        
                        accumulated_chars += len(sl) + 1
                        y_pos += 20
                        
            virtual_surface.set_clip(None)
                
            if search_input_active and active_input_field == "lyrics" and (time.time() % 1.0 < 0.5):
                if cursor_y + 16 <= lyrics_textarea_rect.bottom and cursor_y >= lyrics_textarea_rect.y:
                    pygame.draw.line(virtual_surface, COLOR_SPOTIFY_GREEN, (cursor_x, cursor_y), (cursor_x, cursor_y + 16), 2)
        else:
            max_lyrics_scroll = 0
            placeholder = font_small.render("Type or paste the song lyrics here... (e.g., [00:12] Synced Line! Press Ctrl+V to paste)", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(placeholder, (lyrics_textarea_rect.x + 15, lyrics_textarea_rect.y + 15))
            
        if is_portrait:
            btn_y = lyrics_textarea_rect.bottom + 20
            start_x = main_x + (main_w - 230) // 2 
            lyrics_close_rect = pygame.Rect(start_x, btn_y, 100, 42)
            lyrics_save_rect = pygame.Rect(start_x + 120, btn_y, 110, 42)
        else:
            lyrics_close_rect = pygame.Rect(main_x + 40, 590, 100, 42)
            lyrics_save_rect = pygame.Rect(main_x + 150, 590, 100, 42)
        
        c_bg = COLOR_HOVER if lyrics_close_rect.collidepoint(mouse_pos) else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, c_bg, lyrics_close_rect, border_radius=21)
        c_txt = font_body.render("Close", True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (lyrics_close_rect.x + 28, lyrics_close_rect.y + 11))
        
        s_bg = (40, 230, 110) if lyrics_save_rect.collidepoint(mouse_pos) else COLOR_SPOTIFY_GREEN
        pygame.draw.rect(virtual_surface, s_bg, lyrics_save_rect, border_radius=21)
        s_txt = font_body.render("Save", True, COLOR_BLACK)
        virtual_surface.blit(s_txt, (lyrics_save_rect.x + 30, lyrics_save_rect.y + 11))
        return

    if show_create_playlist_modal:
        if is_browsing_for_cover:
            draw_main_content()
            return

        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT))
        
        lbl = font_huge.render("Create playlist", True, COLOR_WHITE)
        if is_portrait:
            virtual_surface.blit(lbl, (main_x + (main_w - lbl.get_width()) // 2, 45))
        else:
            virtual_surface.blit(lbl, (main_x + 50, 60))
        
        if is_portrait:
            img_x = main_x + (main_w - 220) // 2
            img_y = 120
        else:
            img_x = main_x + 50
            img_y = 160
            
        modal_image_picker_rect = pygame.Rect(img_x, img_y, 220, 220)
        if modal_playlist_cover_surface:
            disp_modal_cover = pygame.transform.smoothscale(modal_playlist_cover_surface, (220, 220))
            virtual_surface.blit(disp_modal_cover, (img_x, img_y))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_image_picker_rect)
            draw_spotify_pencil(virtual_surface, img_x + 110, img_y + 110, COLOR_BLACK)
            
        draw_unified_cover_overlay(virtual_surface, modal_image_picker_rect, mouse_pos)
            
        label_meta = font_small.render("Name", True, COLOR_TEXT_MUTED)
        
        input_x = main_x + 300 if not is_portrait else main_x + 50
        input_y = 185 if not is_portrait else 405
        input_w = main_w - 330 if not is_portrait else main_w - 100
        
        virtual_surface.blit(label_meta, (input_x, input_y - 25))
        
        modal_input_rect = pygame.Rect(input_x, input_y, input_w, 42)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, modal_input_rect, border_radius=6)
        if search_input_active and active_input_field == "name":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_input_rect, width=2, border_radius=6)
            
        if playlist_input_text:
            text_surf = font_body.render(playlist_input_text, True, COLOR_WHITE)
        else:
            text_surf = font_body.render("My Playlist #1", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(text_surf, (modal_input_rect.x + 15, modal_input_rect.y + 11))
        
        label_desc = font_small.render("Description", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(label_desc, (input_x, input_y + 60))
        
        modal_desc_rect = pygame.Rect(input_x, input_y + 85, input_w, 110)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, modal_desc_rect, border_radius=6)
        if search_input_active and active_input_field == "description":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_desc_rect, width=2, border_radius=6)
            
        if playlist_desc_text:
            wrapped_lines = get_wrapped_lines(playlist_desc_text, font_small, input_w - 30)
            y_text_line = modal_desc_rect.y + 12
            for line in wrapped_lines:
                if y_text_line + 18 <= modal_desc_rect.bottom:
                    line_surf = font_small.render(line, True, COLOR_WHITE)
                    virtual_surface.blit(line_surf, (modal_desc_rect.x + 15, y_text_line))
                    y_text_line += 18
        else:
            desc_surf = font_small.render("Add an optional description", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(desc_surf, (modal_desc_rect.x + 15, modal_desc_rect.y + 12))
        
        desc_lbl = font_small.render("Personalize your new local playlist with a clean title and custom description.", True, COLOR_WHITE)
        if not is_portrait:
            virtual_surface.blit(desc_lbl, (main_x + 50, 415))
        else:
            lbl_x = main_x + (main_w - desc_lbl.get_width()) // 2
            virtual_surface.blit(desc_lbl, (max(main_x + 10, lbl_x), input_y + 215))
        
        if is_portrait:
            btn_y = input_y + 250
            start_x = main_x + (main_w - 220) // 2
            modal_close_rect = pygame.Rect(start_x, btn_y, 100, 42)
            modal_save_rect = pygame.Rect(start_x + 120, btn_y, 100, 42)
        else:
            btn_y = 460
            modal_close_rect = pygame.Rect(main_x + 50, btn_y, 100, 42)
            modal_save_rect = pygame.Rect(main_x + 170, btn_y, 100, 42)
        
        c_bg = COLOR_HOVER if modal_close_rect.collidepoint(mouse_pos) else COLOR_CARD_BG
        pygame.draw.rect(virtual_surface, c_bg, modal_close_rect, border_radius=21)
        c_txt = font_body.render("Cancel", True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (modal_close_rect.x + 24, modal_close_rect.y + 11))
        
        s_bg = (40, 230, 110) if modal_save_rect.collidepoint(mouse_pos) else COLOR_SPOTIFY_GREEN
        pygame.draw.rect(virtual_surface, s_bg, modal_save_rect, border_radius=21)
        s_txt = font_body.render("Save", True, COLOR_BLACK)
        virtual_surface.blit(s_txt, (modal_save_rect.x + 32, modal_save_rect.y + 11))

    elif show_add_to_playlist_modal:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, main_h))
        
        lbl = font_title.render("Pick a playlist to add it to", True, COLOR_WHITE)
        virtual_surface.blit(lbl, (content_pad_x, 40))
        
        track_lbl_text = f"Song: {track_to_add_to_playlist['title']}" if track_to_add_to_playlist else ""
        track_lbl = font_small.render(track_lbl_text, True, COLOR_TEXT_MUTED)
        virtual_surface.blit(track_lbl, (content_pad_x, 70))
        
        modal_close_rect = pygame.Rect(main_x + main_w - 110, 35, 90, 35)
        c_bg = COLOR_HOVER if modal_close_rect.collidepoint(mouse_pos) else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, c_bg, modal_close_rect, border_radius=15)
        c_txt = font_small.render("Cancel", True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (modal_close_rect.x + 23, modal_close_rect.y + 8))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)
        
        modal_playlist_rects = []
        p_names = list(custom_playlists.keys())
        
        if not p_names:
            empty_lbl = font_body.render("No custom playlists built yet.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_lbl, (content_pad_x, 150))
            hint_lbl = font_small.render("Go to 'Your Library' and tap '+' to create one.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(hint_lbl, (content_pad_x, 180))
            max_music_scroll = 0
        else:
            total_content_height = len(p_names) * 55
            max_music_scroll = max(0, total_content_height - (main_h - 130) + 30)
            
            clip_rect = pygame.Rect(main_x, 130, main_w, main_h - 130)
            virtual_surface.set_clip(clip_rect)
            
            y_item = 130 - int(music_grid_scroll_offset)
            for p_name in p_names:
                item_rect = pygame.Rect(main_x + 20, y_item, main_w - 50, 45)
                if item_rect.colliderect(clip_rect):
                    modal_playlist_rects.append((item_rect, p_name))
                    
                    if item_rect.collidepoint(mouse_pos):
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=6)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, item_rect, border_radius=6)
                        
                    p_lbl = font_body.render(f" ♫  {p_name}", True, COLOR_WHITE)
                    virtual_surface.blit(p_lbl, (item_rect.x + 15, item_rect.y + 12))
                    
                    count_lbl = font_small.render(f"{len(custom_playlists[p_name]['tracks'])} tracks", True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(count_lbl, (main_x + main_w - 140, item_rect.y + 14))
                y_item += 55
            virtual_surface.set_clip(None)

def draw_media_bar():
    global play_btn_rect, prev_btn_rect, next_btn_rect, minus_10_btn_rect, plus_10_btn_rect, mediabar_add_btn_rect, mediabar_lyrics_btn_rect, star_btn_rect, shuffle_btn_rect, progress_bar_rect
    
    if current_track["title"] == "Select a song" or show_lyrics_editor_view or show_create_playlist_modal:
        return

    bar_height = 130 if is_portrait else 90
    bar_rect = pygame.Rect(0, HEIGHT - bar_height, WIDTH, bar_height)
    pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, bar_rect)
    
    now_playing_title = font_body.render(current_track["title"] if len(current_track["title"]) < 20 else current_track["title"][:17] + "...", True, COLOR_WHITE)
    now_playing_artist = font_small.render(current_track["artist"] if len(current_track["artist"]) < 20 else current_track["artist"][:17] + "...", True, COLOR_TEXT_MUTED)
    virtual_surface.blit(now_playing_title, (20, HEIGHT - bar_height + 25))
    virtual_surface.blit(now_playing_artist, (20, HEIGHT - bar_height + 45)) 
    
    center_x = WIDTH // 2 
    center_y = HEIGHT - (90 if is_portrait else 60) 
    btn_offset_x = center_x
    
    star_btn_rect = pygame.Rect(btn_offset_x - 130, center_y - 10, 20, 20)
    mouse_pos = get_virtual_mouse_pos()
    
    is_starred = current_track in liked_tracks
    is_star_hovered = star_btn_rect.collidepoint(mouse_pos)
    is_star_clicked = is_star_hovered and pygame.mouse.get_pressed()[0]
    
    if is_star_clicked:
        star_color = (20, 150, 65) if is_starred else COLOR_SPOTIFY_GREEN
    elif is_star_hovered:
        star_color = COLOR_WHITE if not is_starred else (40, 230, 110)
    else:
        star_color = COLOR_SPOTIFY_GREEN if is_starred else COLOR_TEXT_MUTED
        
    draw_manual_thumbs_up(virtual_surface, star_btn_rect.x, star_btn_rect.y, star_btn_rect.width, star_btn_rect.height, star_color)

    mediabar_lyrics_btn_rect = pygame.Rect(btn_offset_x - 165, center_y - 14, 28, 28) 
    mediabar_add_btn_rect    = pygame.Rect(btn_offset_x - 95, center_y - 14, 28, 28)
    minus_10_btn_rect        = pygame.Rect(btn_offset_x - 55, center_y - 16, 32, 32)
    prev_btn_rect            = pygame.Rect(btn_offset_x - 18, center_y - 18, 28, 36)
    play_btn_rect            = pygame.Rect(btn_offset_x + 15, center_y - 18, 36, 36)
    next_btn_rect            = pygame.Rect(btn_offset_x + 56, center_y - 18, 28, 36)
    plus_10_btn_rect         = pygame.Rect(btn_offset_x + 90, center_y - 16, 32, 32)
    shuffle_btn_rect         = pygame.Rect(btn_offset_x + 132, center_y - 16, 32, 32)

    lyrics_hover = mediabar_lyrics_btn_rect.collidepoint(mouse_pos)
    lyrics_click = lyrics_hover and pygame.mouse.get_pressed()[0]
    
    if lyrics_click:
        paper_icon_color = COLOR_SPOTIFY_GREEN
    elif lyrics_hover:
        paper_icon_color = COLOR_WHITE
    else:
        paper_icon_color = COLOR_TEXT_MUTED
    draw_piece_of_paper_icon(virtual_surface, mediabar_lyrics_btn_rect, paper_icon_color)

    add_hover = mediabar_add_btn_rect.collidepoint(mouse_pos)
    add_click = add_hover and pygame.mouse.get_pressed()[0]
    
    if add_click:
        pygame.draw.circle(virtual_surface, (20, 150, 65), mediabar_add_btn_rect.center, 13)
        plus_color = COLOR_WHITE
    elif add_hover:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, mediabar_add_btn_rect.center, 14)
        plus_color = COLOR_BLACK
    else:
        pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, mediabar_add_btn_rect.center, 13, width=2)
        plus_color = COLOR_TEXT_MUTED
        
    plus_surf = font_body.render("+", True, plus_color)
    plus_x = mediabar_add_btn_rect.centerx - plus_surf.get_width() // 2
    plus_y = mediabar_add_btn_rect.centery - plus_surf.get_height() // 2 - 2
    virtual_surface.blit(plus_surf, (plus_x, plus_y))

    m10_hover = minus_10_btn_rect.collidepoint(mouse_pos)
    m10_click = m10_hover and pygame.mouse.get_pressed()[0]
    
    if m10_click:
        pygame.draw.circle(virtual_surface, (20, 150, 65), minus_10_btn_rect.center, 16)
        pygame.draw.circle(virtual_surface, COLOR_WHITE, minus_10_btn_rect.center, 16, width=2)
        m10_text_color = COLOR_WHITE
    elif m10_hover:
        pygame.draw.circle(virtual_surface, COLOR_HOVER, minus_10_btn_rect.center, 16)
        pygame.draw.circle(virtual_surface, COLOR_WHITE, minus_10_btn_rect.center, 16, width=2)
        m10_text_color = COLOR_WHITE
    else:
        pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, minus_10_btn_rect.center, 16, width=2)
        m10_text_color = COLOR_TEXT_MUTED
        
    m10_surf = font_small.render("-10", True, m10_text_color)
    virtual_surface.blit(m10_surf, (minus_10_btn_rect.centerx - m10_surf.get_width() // 2, minus_10_btn_rect.centery - m10_surf.get_height() // 2))

    prev_hover = prev_btn_rect.collidepoint(mouse_pos)
    prev_click = prev_hover and pygame.mouse.get_pressed()[0]
    prev_color = COLOR_SPOTIFY_GREEN if prev_click else (COLOR_WHITE if prev_hover else COLOR_TEXT_MUTED)
    pygame.draw.polygon(virtual_surface, prev_color, [(btn_offset_x - 15, center_y), (btn_offset_x, center_y - 9), (btn_offset_x, center_y + 9)])
    
    is_mb_play_hovered = play_btn_rect.collidepoint(mouse_pos)
    is_mb_play_pressed = is_mb_play_hovered and pygame.mouse.get_pressed()[0] 

    if is_mb_play_pressed:
        pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, (btn_offset_x + 33, center_y), 16)
    elif is_mb_play_hovered:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, (btn_offset_x + 33, center_y), 20)
    else:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, (btn_offset_x + 33, center_y), 18)
    
    if not is_playing:
        pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(btn_offset_x + 30, center_y - 6), (btn_offset_x + 30, center_y + 6), (btn_offset_x + 40, center_y)])
    else:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (btn_offset_x + 29, center_y - 6, 3, 12))
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (btn_offset_x + 35, center_y - 6, 3, 12))

    next_hover = next_btn_rect.collidepoint(mouse_pos)
    next_click = next_hover and pygame.mouse.get_pressed()[0]
    next_color = COLOR_SPOTIFY_GREEN if next_click else (COLOR_WHITE if next_hover else COLOR_TEXT_MUTED)
    pygame.draw.polygon(virtual_surface, next_color, [(btn_offset_x + 80, center_y), (btn_offset_x + 65, center_y - 9), (btn_offset_x + 65, center_y + 9)])
    
    p10_hover = plus_10_btn_rect.collidepoint(mouse_pos)
    p10_click = p10_hover and pygame.mouse.get_pressed()[0]
    
    if p10_click:
        pygame.draw.circle(virtual_surface, (20, 150, 65), plus_10_btn_rect.center, 16)
        pygame.draw.circle(virtual_surface, COLOR_WHITE, plus_10_btn_rect.center, 16, width=2)
        p10_text_color = COLOR_WHITE
    elif p10_hover:
        pygame.draw.circle(virtual_surface, COLOR_HOVER, plus_10_btn_rect.center, 16)
        pygame.draw.circle(virtual_surface, COLOR_WHITE, plus_10_btn_rect.center, 16, width=2)
        p10_text_color = COLOR_WHITE
    else:
        pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, plus_10_btn_rect.center, 16, width=2)
        p10_text_color = COLOR_TEXT_MUTED
        
    p10_surf = font_small.render("+10", True, p10_text_color)
    virtual_surface.blit(p10_surf, (plus_10_btn_rect.centerx - p10_surf.get_width() // 2, plus_10_btn_rect.centery - p10_surf.get_height() // 2))

    sh_hover = shuffle_btn_rect.collidepoint(mouse_pos)
    if is_shuffle:
        sh_icon_color = COLOR_SPOTIFY_GREEN
        pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (shuffle_btn_rect.centerx, shuffle_btn_rect.centery + 12), 2)
    else:
        sh_icon_color = COLOR_WHITE if sh_hover else COLOR_TEXT_MUTED
    draw_spotify_shuffle_icon(virtual_surface, shuffle_btn_rect, sh_icon_color)

    progress_bar_width = min(400, WIDTH - 40) if is_portrait else 400
    progress_bar_x = center_x - (progress_bar_width // 2) if is_portrait else btn_offset_x - (progress_bar_width // 2) + 20
    progress_bar_y = HEIGHT - (50 if is_portrait else 25)
    progress_bar_rect = pygame.Rect(progress_bar_x, progress_bar_y - 10, progress_bar_width, 24)
    
    elapsed_sec = 0.0
    remaining_sec = 0.0
    percent_fill = 0.0
    
    if is_dragging_progress:
        elapsed_sec = min(track_duration, drag_seek_target)
        remaining_sec = max(0.0, track_duration - elapsed_sec)
        percent_fill = min(1.0, max(0.0, elapsed_sec / track_duration))
    elif track_duration > 0 and music_loaded:
        if current_backend =="android" and android_media_player:
            try: elapsed_sec = android_media_player.getCurrentPosition() / 1000.0
            except: elapsed_sec = 0.0
        else:
            mix_pos = pygame.mixer.music.get_pos()
            if mix_pos == -1:
                elapsed_sec = track_duration if current_track.get("_has_started", False) else track_start_accumulator
            else:
                elapsed_sec = track_start_accumulator + (mix_pos / 1000.0)
            
        elapsed_sec = min(track_duration, elapsed_sec)
        remaining_sec = max(0.0, track_duration - elapsed_sec)
        percent_fill = min(1.0, max(0.0, elapsed_sec / track_duration))

    pygame.draw.rect(virtual_surface, COLOR_HOVER, (progress_bar_x, progress_bar_y, progress_bar_width, 4), border_radius=2)
    pygame.draw.rect(virtual_surface, COLOR_WHITE, (progress_bar_x, progress_bar_y, int(progress_bar_width * percent_fill), 4), border_radius=2)
    
    el_min, el_sec = int(elapsed_sec) // 60, int(elapsed_sec) % 60
    rem_min, rem_sec = int(remaining_sec) // 60, int(remaining_sec) % 60
    
    time_start = font_small.render(f"{el_min}:{el_sec:02d}", True, COLOR_TEXT_MUTED)
    time_end = font_small.render(f"-{rem_min}:{rem_sec:02d}" if track_duration > 0 else "0:00", True, COLOR_TEXT_MUTED)
    
    virtual_surface.blit(time_start, (progress_bar_x - 35, progress_bar_y - 6))
    virtual_surface.blit(time_end, (progress_bar_x + progress_bar_width + 10, progress_bar_y - 6))

    track_ref = current_track.get("path", "")
    current_lyrics_str = song_lyrics_database.get(track_ref, "")
    if current_lyrics_str:
        lyric_lines = current_lyrics_str.split('\n')
        active_lyric_text = ""
        best_time = -1
        for line in lyric_lines:
            line_stripped = line.strip()
            if line_stripped.startswith('[') and ']' in line_stripped:
                try:
                    time_part, lyric_part = line_stripped.split(']', 1)
                    time_part = time_part[1:].strip()
                    if ':' in time_part:
                        t_parts = time_part.split(':')
                        lyric_time = float(t_parts[0]) * 60 + float(t_parts[1])
                        if lyric_time <= elapsed_sec and lyric_time > best_time:
                            best_time = lyric_time
                            active_lyric_text = lyric_part.strip()
                except:
                    pass
        if active_lyric_text:
            lyric_surf = font_small.render(active_lyric_text, True, COLOR_SPOTIFY_GREEN)
            if is_portrait:
                virtual_surface.blit(lyric_surf, ((WIDTH - lyric_surf.get_width()) // 2, HEIGHT - 30))
            else:
                virtual_surface.blit(lyric_surf, (WIDTH - lyric_surf.get_width() - 30, HEIGHT - 55))

# --- MAIN LOOP ---
load_app_data()
running = True

virtual_keyboard_active = False

while running:
    if search_input_active and not virtual_keyboard_active:
        try: pygame.key.start_text_input()
        except: pass
        virtual_keyboard_active = True
    elif not search_input_active and virtual_keyboard_active:
        try: pygame.key.stop_text_input()
        except: pass
        virtual_keyboard_active = False

    dt = min(0.1, clock.get_time() / 1000.0)
    
    music_grid_scroll_offset += (target_music_scroll - music_grid_scroll_offset) * (15.0 * dt)
    browser_scroll_offset += (target_browser_scroll - browser_scroll_offset) * (15.0 * dt)
    settings_scroll_offset += (target_settings_scroll - settings_scroll_offset) * (15.0 * dt)
    lyrics_scroll_offset += (target_lyrics_scroll - lyrics_scroll_offset) * (15.0 * dt)

    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
            
        elif event.type == pygame.VIDEORESIZE:
            REAL_WIDTH, REAL_HEIGHT = event.w, event.h
            screen = pygame.display.set_mode((REAL_WIDTH, REAL_HEIGHT), pygame.FULLSCREEN | pygame.RESIZABLE)
            is_portrait = REAL_HEIGHT > REAL_WIDTH
            WIDTH, HEIGHT = (700, 1100) if is_portrait else (1100, 700)
            virtual_surface = pygame.Surface((WIDTH, HEIGHT))
            
        elif event.type == pygame.TEXTINPUT:
            if search_input_active:
                if show_lyrics_editor_view and active_input_field == "lyrics":
                    track_ref = current_track.get("path", "")
                    txt = song_lyrics_database.get(track_ref, "")
                    if lyrics_cursor_pos > len(txt): lyrics_cursor_pos = len(txt)
                    new_txt = txt[:lyrics_cursor_pos] + event.text + txt[lyrics_cursor_pos:]
                    song_lyrics_database[track_ref] = new_txt
                    lyrics_cursor_pos += len(event.text)
                    lyrics_text_changed = True
                elif show_create_playlist_modal:
                    if active_input_field == "name" and len(playlist_input_text) < 20:
                        playlist_input_text += event.text
                    elif active_input_field == "description":
                        lines_test = get_wrapped_lines(playlist_desc_text + event.text, font_small, 420)
                        if len(lines_test) * 18 <= 90:
                            playlist_desc_text += event.text
                elif current_page == "Search" and not is_browsing_storage and not viewing_settings_page:
                    if len(search_query) < 25:
                        search_query += event.text

        elif event.type == pygame.KEYDOWN:
            mods = pygame.key.get_mods()
            is_ctrl_or_cmd = (mods & pygame.KMOD_CTRL) or (mods & pygame.KMOD_META)
            
            if is_ctrl_or_cmd and event.key == pygame.K_v and search_input_active:
                pasted_text = get_clipboard_text()
                
                if pasted_text:
                    if show_lyrics_editor_view and active_input_field == "lyrics":
                        track_ref = current_track.get("path", "")
                        txt = song_lyrics_database.get(track_ref, "")
                        if lyrics_cursor_pos > len(txt): lyrics_cursor_pos = len(txt)
                        song_lyrics_database[track_ref] = txt[:lyrics_cursor_pos] + pasted_text + txt[lyrics_cursor_pos:]
                        lyrics_cursor_pos += len(pasted_text)
                        lyrics_text_changed = True
                    elif show_create_playlist_modal:
                        if active_input_field == "name":
                            playlist_input_text = (playlist_input_text + pasted_text)[:20]
                        elif active_input_field == "description":
                            playlist_desc_text += pasted_text
                    elif current_page == "Search" and not is_browsing_storage and not viewing_settings_page:
                        search_query = (search_query + pasted_text)[:25]
                continue

            if show_lyrics_editor_view and search_input_active and active_input_field == "lyrics":
                track_ref = current_track.get("path", "")
                lyrics_txt = song_lyrics_database.get(track_ref, "")
                if lyrics_cursor_pos > len(lyrics_txt): lyrics_cursor_pos = len(lyrics_txt)
                
                if event.key == pygame.K_BACKSPACE:
                    if lyrics_cursor_pos > 0:
                        song_lyrics_database[track_ref] = lyrics_txt[:lyrics_cursor_pos - 1] + lyrics_txt[lyrics_cursor_pos:]
                        lyrics_cursor_pos -= 1
                        lyrics_text_changed = True
                elif event.key == pygame.K_DELETE:
                    if lyrics_cursor_pos < len(lyrics_txt):
                        song_lyrics_database[track_ref] = lyrics_txt[:lyrics_cursor_pos] + lyrics_txt[lyrics_cursor_pos + 1:]
                        lyrics_text_changed = True
                elif event.key == pygame.K_RETURN:
                    song_lyrics_database[track_ref] = lyrics_txt[:lyrics_cursor_pos] + "\n" + lyrics_txt[lyrics_cursor_pos:]
                    lyrics_cursor_pos += 1
                    lyrics_text_changed = True
                elif event.key == pygame.K_LEFT:
                    if lyrics_cursor_pos > 0:
                        lyrics_cursor_pos -= 1
                elif event.key == pygame.K_RIGHT:
                    if lyrics_cursor_pos < len(lyrics_txt):
                        lyrics_cursor_pos += 1
                elif event.key == pygame.K_UP:
                    lines_before = lyrics_txt[:lyrics_cursor_pos].split('\n')
                    if len(lines_before) > 1:
                        current_line_offset = len(lines_before[-1])
                        prev_line_len = len(lines_before[-2])
                        target_offset = min(current_line_offset, prev_line_len)
                        lyrics_cursor_pos = len('\n'.join(lines_before[:-1])) - prev_line_len + target_offset
                elif event.key == pygame.K_DOWN:
                    lines_before = lyrics_txt[:lyrics_cursor_pos].split('\n')
                    lines_after = lyrics_txt[lyrics_cursor_pos:].split('\n')
                    if len(lines_after) > 1:
                        current_line_offset = len(lines_before[-1])
                        next_line_len = len(lines_after[1])
                        target_offset = min(current_line_offset, next_line_len)
                        lyrics_cursor_pos = len(lyrics_txt[:lyrics_cursor_pos]) + len(lines_after[0]) + 1 + target_offset
                elif event.key == pygame.K_ESCAPE:
                    search_input_active = False
                        
            elif show_create_playlist_modal and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    if active_input_field == "name":
                        playlist_input_text = playlist_input_text[:-1]
                    else:
                        playlist_desc_text = playlist_desc_text[:-1]
                elif event.key == pygame.K_RETURN:
                    search_input_active = False
            
            elif current_page == "Search" and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    search_query = search_query[:-1]
                elif event.key == pygame.K_ESCAPE or event.key == pygame.K_RETURN:
                    search_input_active = False
                        
        elif event.type == pygame.MOUSEBUTTONDOWN:
            mouse_pos = get_virtual_mouse_pos()
            
            if current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal:
                if progress_bar_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                    if event.button == 1:
                        is_dragging_progress = True
                        relative_x = mouse_pos[0] - progress_bar_rect.x
                        fraction = min(1.0, max(0.0, relative_x / progress_bar_rect.width))
                        drag_seek_target = fraction * track_duration
                        continue

            if show_lyrics_editor_view:
                if event.button == 4: target_lyrics_scroll = max(0.0, target_lyrics_scroll - 120.0)
                elif event.button == 5: target_lyrics_scroll = min(max_lyrics_scroll, target_lyrics_scroll + 120.0)
            elif not show_create_playlist_modal:
                if show_add_to_playlist_modal or current_page == "Search" or (current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name)):
                    if is_browsing_storage or is_browsing_for_cover:
                        if event.button == 4: target_browser_scroll = max(0.0, target_browser_scroll - 120.0)
                        elif event.button == 5: target_browser_scroll = min(max_browser_scroll, target_browser_scroll + 120.0)
                    elif viewing_settings_page:
                        if event.button == 4: target_settings_scroll = max(0.0, target_settings_scroll - 120.0)
                        elif event.button == 5: target_settings_scroll = min(max_settings_scroll, target_settings_scroll + 120.0)
                    else:
                        if event.button == 4: target_music_scroll = max(0.0, target_music_scroll - 150.0)
                        elif event.button == 5: target_music_scroll = min(max_music_scroll, target_music_scroll + 150.0)
            elif show_create_playlist_modal and is_browsing_for_cover:
                if event.button == 4: target_browser_scroll = max(0.0, target_browser_scroll - 120.0)
                elif event.button == 5: target_browser_scroll = min(max_browser_scroll, target_browser_scroll + 120.0)

            if event.button == 3 and current_page == "Search" and not is_browsing_storage and not viewing_settings_page and not (show_create_playlist_modal or show_add_to_playlist_modal or show_lyrics_editor_view):
                for rect, track in track_rects:
                    if rect.collidepoint(mouse_pos):
                        track_to_add_to_playlist = track
                        show_add_to_playlist_modal = True
                        target_music_scroll = 0.0
                        break

            if event.button == 1:
                is_dragging_grid = True
                last_touch_y = mouse_pos[1]
                total_drag_dy = 0
                
        elif event.type == pygame.MOUSEMOTION:
            mouse_pos = get_virtual_mouse_pos()
            
            if is_dragging_progress:
                relative_x = mouse_pos[0] - progress_bar_rect.x
                fraction = min(1.0, max(0.0, relative_x / progress_bar_rect.width))
                drag_seek_target = fraction * track_duration
            elif is_dragging_grid:
                dy = last_touch_y - mouse_pos[1]
                total_drag_dy += abs(dy)
                
                if show_create_playlist_modal:
                    if is_browsing_for_cover:
                        target_browser_scroll += dy * 1.5
                        target_browser_scroll = max(0.0, min(max_browser_scroll, target_browser_scroll))
                        last_touch_y = mouse_pos[1]
                elif show_lyrics_editor_view:
                    target_lyrics_scroll += dy * 1.5
                    target_lyrics_scroll = max(0.0, min(max_lyrics_scroll, target_lyrics_scroll))
                    last_touch_y = mouse_pos[1]
                else:
                    if show_add_to_playlist_modal or current_page == "Search" or (current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name)):
                        if is_browsing_storage or is_browsing_for_cover:
                            target_browser_scroll += dy * 1.5
                            target_browser_scroll = max(0.0, min(max_browser_scroll, target_browser_scroll))
                            last_touch_y = mouse_pos[1]
                        elif viewing_settings_page:
                            target_settings_scroll += dy * 1.5
                            target_settings_scroll = max(0.0, min(max_settings_scroll, target_settings_scroll))
                            last_touch_y = mouse_pos[1]
                        else:
                            target_music_scroll += dy * 1.5
                            target_music_scroll = max(0.0, min(max_music_scroll, target_music_scroll))
                            last_touch_y = mouse_pos[1]

        elif event.type == pygame.MOUSEBUTTONUP:
            mouse_pos = get_virtual_mouse_pos()
            if event.button == 1:
                if is_dragging_progress:
                    is_dragging_progress = False
                    track_start_accumulator = drag_seek_target
                    current_track["_has_started"] = False
                    if current_backend == "android" and android_media_player:
                        try:
                            android_media_player.seekTo(int(drag_seek_target * 1000))
                            android_media_player.start()
                        except: pass
                    else:
                        try: pygame.mixer.music.play(start=drag_seek_target)
                        except: pass
                    is_playing = True
                    continue 

                is_dragging_grid = False
                
                if total_drag_dy < 15:
                    if show_lyrics_editor_view:
                        if lyrics_close_rect.collidepoint(mouse_pos):
                            show_lyrics_editor_view = False
                            search_input_active = False
                        elif lyrics_save_rect.collidepoint(mouse_pos):
                            show_lyrics_editor_view = False
                            search_input_active = False
                            save_app_data()
                        elif lyrics_textarea_rect.collidepoint(mouse_pos):
                            search_input_active = True
                            active_input_field = "lyrics"
                        else:
                            search_input_active = False
                        continue

                    if show_create_playlist_modal:
                        if is_browsing_for_cover:
                            if cancel_browser_btn_rect.collidepoint(mouse_pos):
                                is_browsing_for_cover = False
                            else:
                                for rect, item in browser_rects:
                                    if rect.collidepoint(mouse_pos):
                                        if item["is_dir"]:
                                            current_browser_path = item["path"]
                                            update_browser_contents()
                                        else:
                                            try:
                                                raw_img = pygame.image.load(item["path"])
                                                modal_playlist_cover_surface = pygame.transform.smoothscale(raw_img, (220, 220))
                                                modal_playlist_cover_path = item["path"]
                                            except Exception as image_err:
                                                print(f"Error importing cover layout graphics: {image_err}")
                                            is_browsing_for_cover = False
                                        break
                            continue

                        if modal_close_rect.collidepoint(mouse_pos):
                            show_create_playlist_modal = False
                            playlist_input_text = ""
                            playlist_desc_text = ""
                            modal_playlist_cover_surface = None
                            modal_playlist_cover_path = None
                            search_input_active = False
                        elif modal_save_rect.collidepoint(mouse_pos):
                            clean_name = playlist_input_text.strip() if playlist_input_text.strip() else "My Playlist"
                            if clean_name not in custom_playlists:
                                final_thumb = None
                                if modal_playlist_cover_surface:
                                    final_thumb = pygame.transform.smoothscale(modal_playlist_cover_surface, (130, 110))
                                custom_playlists[clean_name] = {
                                    "tracks": [], 
                                    "image_path": modal_playlist_cover_path, 
                                    "surface": final_thumb,
                                    "description": playlist_desc_text.strip()
                                }
                            playlist_input_text = ""
                            playlist_desc_text = ""
                            modal_playlist_cover_surface = None
                            modal_playlist_cover_path = None
                            show_create_playlist_modal = False
                            search_input_active = False
                            save_app_data()
                        elif modal_input_rect.collidepoint(mouse_pos):
                            search_input_active = True
                            active_input_field = "name"
                        elif modal_desc_rect.collidepoint(mouse_pos):
                            search_input_active = True
                            active_input_field = "description"
                        elif modal_image_picker_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "create"
                            update_browser_contents()
                        else:
                            search_input_active = False
                        continue
                        
                    elif show_add_to_playlist_modal:
                        if modal_close_rect.collidepoint(mouse_pos):
                            show_add_to_playlist_modal = False
                            track_to_add_to_playlist = None
                            target_music_scroll = 0.0
                        else:
                            for rect, p_name in modal_playlist_rects:
                                if rect.collidepoint(mouse_pos):
                                    if track_to_add_to_playlist and track_to_add_to_playlist not in custom_playlists[p_name]["tracks"]:
                                        custom_playlists[p_name]["tracks"].append(track_to_add_to_playlist)
                                    show_add_to_playlist_modal = False
                                    track_to_add_to_playlist = None
                                    target_music_scroll = 0.0 
                                    save_app_data()
                                    break
                        continue

                    if current_page == "Search" and viewing_settings_page and saved_directories:
                        clicked_panel_item = False
                        for rect, d_path in settings_dir_rects:
                            if rect.collidepoint(mouse_pos):
                                saved_directories.remove(d_path)
                                rebuild_imported_tracks()
                                clicked_panel_item = True
                                save_app_data()
                                break
                        if clicked_panel_item:
                            continue

                    if current_page == "Search" and not is_browsing_storage and not viewing_settings_page and search_box_rect.collidepoint(mouse_pos):
                        search_input_active = True
                    else:
                        if not show_create_playlist_modal:
                            search_input_active = False

                    for rect, target_page in sidebar_rects:
                        if rect.collidepoint(mouse_pos):
                            current_page = target_page
                            is_browsing_storage = False 
                            is_browsing_for_cover = False
                            viewing_liked_playlist = False
                            selected_custom_playlist_name = None
                            viewing_settings_page = False
                            target_music_scroll = 0.0
                            target_browser_scroll = 0.0
                            target_settings_scroll = 0.0
                            target_lyrics_scroll = 0.0

                    if is_browsing_for_cover and current_page == "Your Library":
                        if cancel_browser_btn_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = False
                        else:
                            for rect, item in browser_rects:
                                if rect.collidepoint(mouse_pos):
                                    if item["is_dir"]:
                                        current_browser_path = item["path"]
                                        update_browser_contents()
                                    else:
                                        try:
                                            raw_img = pygame.image.load(item["path"])
                                            scaled_surf = pygame.transform.smoothscale(raw_img, (130, 110))
                                            if browsing_cover_target == "custom_view":
                                                custom_playlists[selected_custom_playlist_name]["image_path"] = item["path"]
                                                custom_playlists[selected_custom_playlist_name]["surface"] = scaled_surf
                                            elif browsing_cover_target == "liked_view":
                                                liked_songs_custom_cover["image_path"] = item["path"]
                                                liked_songs_custom_cover["surface"] = scaled_surf
                                            save_app_data()
                                        except Exception as image_err:
                                            print(f"Error importing cover layout graphics: {image_err}")
                                        is_browsing_for_cover = False
                                    break
                        continue

                    if (viewing_liked_playlist or selected_custom_playlist_name) and current_page == "Your Library":
                        p_title_text = selected_custom_playlist_name if selected_custom_playlist_name else "Liked Songs"
                        if playlist_cover_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "custom_view" if selected_custom_playlist_name else "liked_view"
                            update_browser_contents()
                            continue
                            
                        if playlist_play_btn_rect.collidepoint(mouse_pos):
                            active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if selected_custom_playlist_name else liked_tracks
                            if active_tracks:
                                is_current_track_in_playlist = any(track["path"] == current_track["path"] for track in active_tracks)
                                if is_current_track_in_playlist and playlist_is_playing == p_title_text:
                                    is_playing = not is_playing
                                    if is_playing:
                                        if current_backend == "android": android_media_player.start()
                                        else: pygame.mixer.music.unpause()
                                    else:
                                        if current_backend == "android": android_media_player.pause()
                                        else: pygame.mixer.music.pause()
                                else:
                                    current_track = active_tracks[0]  
                                    playlist_is_playing = p_title_text  
                                    is_playing = True
                                    green_toggled_tracks.add(current_track["path"])
                                    load_and_play_track(current_track["path"])

                        if playlist_random_btn_rect.collidepoint(mouse_pos):
                            active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if selected_custom_playlist_name else liked_tracks
                            if active_tracks:
                                is_shuffle = not is_shuffle
                                playlist_is_playing = p_title_text
                                if is_shuffle:
                                    random_index = random.randint(0, len(active_tracks) - 1)
                                    current_track = active_tracks[random_index]
                                    is_playing = True
                                    green_toggled_tracks.add(current_track["path"])
                                    load_and_play_track(current_track["path"])

                    if current_page == "Your Library" and not viewing_liked_playlist and not selected_custom_playlist_name:
                        if create_playlist_btn_rect.collidepoint(mouse_pos):
                            show_create_playlist_modal = True
                        elif liked_songs_card_rect.collidepoint(mouse_pos):
                            viewing_liked_playlist = True
                            target_music_scroll = 0.0
                        else:
                            for rect, name in custom_playlist_rects:
                                if rect.collidepoint(mouse_pos):
                                    selected_custom_playlist_name = name
                                    target_music_scroll = 0.0
                                    marquee_offset = 0.0
                                    marquee_direction = 1
                                    break

                    if is_browsing_storage and current_page == "Search":
                        if select_folder_btn_rect.collidepoint(mouse_pos):
                            scan_confirmed_directory(current_browser_path)
                        elif cancel_browser_btn_rect.collidepoint(mouse_pos):
                            is_browsing_storage = False
                        else:
                            for rect, item in browser_rects:
                                if rect.collidepoint(mouse_pos) and item["is_dir"]:
                                    current_browser_path = item["path"]
                                    update_browser_contents()
                                    break
                                    
                    elif viewing_settings_page and current_page == "Search":
                        if close_settings_btn_rect.collidepoint(mouse_pos):
                            viewing_settings_page = False
                    else:
                        if current_page == "Search" and add_folder_btn_rect.collidepoint(mouse_pos):
                            is_browsing_storage = True
                            viewing_settings_page = False
                            update_browser_contents()
                        
                        if current_page == "Search" and saved_directories and settings_btn_rect.collidepoint(mouse_pos):
                            viewing_settings_page = True
                            target_settings_scroll = 0.0
                                
                        if current_page in ["Search"] or (current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name)):
                            for rect, track in track_rects:
                                portrait_sidebar_h = 65 if is_portrait else 0
                                main_x = 0 if is_portrait else 230
                                main_w = WIDTH - main_x
                                
                                event_margin = (130 if is_portrait else 90) if current_track["title"] != "Select a song" else 0
                                main_h_event = HEIGHT - event_margin - portrait_sidebar_h
                                
                                if current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name):
                                    clip_rect_bounds = pygame.Rect(main_x, 315, main_w, main_h_event - 315)
                                else:
                                    clip_rect_bounds = pygame.Rect(main_x, 140, main_w, main_h_event - 140)
                                    
                                if clip_rect_bounds.collidepoint(mouse_pos) and rect.collidepoint(mouse_pos):
                                    current_track = track
                                    playlist_is_playing = (selected_custom_playlist_name if selected_custom_playlist_name else "Liked Songs") if (viewing_liked_playlist or selected_custom_playlist_name) else None
                                    is_playing = True 
                                    green_toggled_tracks.add(current_track["path"])
                                    load_and_play_track(current_track["path"])
                                    
                        if current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal:
                            if mediabar_lyrics_btn_rect.collidepoint(mouse_pos):
                                show_lyrics_editor_view = True
                                track_ref = current_track.get("path", "")
                                if track_ref not in song_lyrics_database:
                                    song_lyrics_database[track_ref] = ""
                                search_input_active = True
                                active_input_field = "lyrics"
                                target_lyrics_scroll = 0.0
                                lyrics_cursor_pos = len(song_lyrics_database[track_ref])

                            if mediabar_add_btn_rect.collidepoint(mouse_pos):
                                track_to_add_to_playlist = current_track
                                show_add_to_playlist_modal = True
                                target_music_scroll = 0.0

                            if minus_10_btn_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                                current_track["_has_started"] = False
                                if current_backend == "android" and android_media_player:
                                    try: current_pos = android_media_player.getCurrentPosition() / 1000.0
                                    except: current_pos = 0.0
                                else:
                                    mix_pos = pygame.mixer.music.get_pos()
                                    current_pos = track_start_accumulator + (mix_pos / 1000.0) if mix_pos != -1 else track_start_accumulator
                                
                                seek_target = max(0.0, current_pos - 10.0)
                                track_start_accumulator = seek_target
                                if current_backend == "android" and android_media_player:
                                    try:
                                        android_media_player.seekTo(int(seek_target * 1000))
                                        android_media_player.start()
                                    except: pass
                                else:
                                    try: pygame.mixer.music.play(start=seek_target)
                                    except: pass
                                is_playing = True

                            if prev_btn_rect.collidepoint(mouse_pos):
                                advance_track(backward=True)

                            if play_btn_rect.collidepoint(mouse_pos):
                                if music_loaded: 
                                    is_playing = not is_playing
                                    if is_playing:
                                        if current_backend == "android": android_media_player.start()
                                        else: pygame.mixer.music.unpause()
                                    else:
                                        if current_backend == "android": android_media_player.pause()
                                        else: pygame.mixer.music.pause()

                            if next_btn_rect.collidepoint(mouse_pos):
                                advance_track(backward=False)

                            if plus_10_btn_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                                current_track["_has_started"] = False
                                if current_backend == "android" and android_media_player:
                                    try: current_pos = android_media_player.getCurrentPosition() / 1000.0
                                    except: current_pos = 0.0
                                else:
                                    mix_pos = pygame.mixer.music.get_pos()
                                    current_pos = track_start_accumulator + (mix_pos / 1000.0) if mix_pos != -1 else track_start_accumulator
                                
                                seek_target = min(track_duration, current_pos + 10.0)
                                track_start_accumulator = seek_target
                                if current_backend == "android" and android_media_player:
                                    try:
                                        android_media_player.seekTo(int(seek_target * 1000))
                                        android_media_player.start()
                                    except: pass
                                else:
                                    try: pygame.mixer.music.play(start=seek_target)
                                    except: pass
                                is_playing = True
                                
                            if shuffle_btn_rect.collidepoint(mouse_pos):
                                is_shuffle = not is_shuffle

                            if star_btn_rect.collidepoint(mouse_pos):
                                if current_track in liked_tracks:
                                    liked_tracks.remove(current_track)
                                else:
                                    liked_tracks.append(current_track)
                                save_app_data()
            
    if is_playing and track_duration > 0 and music_loaded and not is_dragging_progress:
        if current_backend == "android" and android_media_player:
            try: elapsed = android_media_player.getCurrentPosition() / 1000.0
            except: elapsed = 0.0
            if elapsed >= track_duration:
                advance_track(backward=False)
        else:
            mix_pos = pygame.mixer.music.get_pos()
            if mix_pos > 500:
                current_track["_has_started"] = True
                
            elapsed = track_start_accumulator + (mix_pos / 1000.0)
            time_elapsed = time.time() - current_track.get("_play_start_time", time.time())
            
            if (current_track.get("_has_started", False) and (mix_pos == -1 or mix_pos == 0 or elapsed >= track_duration - 0.5)) or (mix_pos == -1 and time_elapsed > 2.0):
                current_track["_has_started"] = False
                advance_track(backward=False)

    virtual_surface.fill(COLOR_BLACK)
    
    draw_main_content()
    draw_sidebar()
    draw_media_bar()
    draw_modals()
    
    # Accurate Letterbox/Pillarbox Screen Scaling
    scale_x = REAL_WIDTH / WIDTH
    scale_y = REAL_HEIGHT / HEIGHT
    scale_factor = min(scale_x, scale_y)
    scaled_w = int(WIDTH * scale_factor)
    scaled_h = int(HEIGHT * scale_factor)
    offset_x = (REAL_WIDTH - scaled_w) // 2
    offset_y = (REAL_HEIGHT - scaled_h) // 2
    
            # Changed smoothscale to standard scale to fix performance issues on high-res displays
    scaled_frame = pygame.transform.scale(virtual_surface, (REAL_WIDTH, REAL_HEIGHT))
    screen.blit(scaled_frame, (0, 0))

    
    pygame.display.flip()
    clock.tick(DEVICE_REFRESH_RATE)

save_app_data()

if TEMP_WAV_PATH and os.path.exists(TEMP_WAV_PATH):
    try: os.remove(TEMP_WAV_PATH)
    except: pass

if HAS_ANDROID_MEDIA and android_media_player:
    try: android_media_player.release()
    except: pass

pygame.quit()
sys.exit()

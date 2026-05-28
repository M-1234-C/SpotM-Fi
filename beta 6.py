import pygame
import sys
import os
import tempfile
import time
import math
import random

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

WIDTH, HEIGHT = 1100, 700

screen = pygame.display.set_mode((REAL_WIDTH, REAL_HEIGHT), pygame.FULLSCREEN)
virtual_surface = pygame.Surface((WIDTH, HEIGHT))
clock = pygame.time.Clock()

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
is_shuffle = False  # Spotify shuffle engine toggle tracker

# Tracker for tracks that have been manually toggled green
green_toggled_tracks = set()

# --- AUDIO TRACKING STATE ---
track_duration = 0.0          
track_start_accumulator = 0.0 
TEMP_WAV_PATH = None          
current_backend = "pygame"    
music_loaded = False          

# Android Native Decoders Initialization
try:
    from jnius import autoclass
    MediaPlayer = autoclass('android.media.MediaPlayer')
    android_media_player = MediaPlayer()
    HAS_ANDROID_MEDIA = True
except:
    android_media_player = None
    HAS_ANDROID_MEDIA = False

# --- DATA STORAGE ---
sidebar_items = ["Search", "Your Library"] 
track_list = []
imported_tracks = []
liked_tracks = []        
saved_directories = []  

# Dynamic Playlist Storage Engine
custom_playlists = {}  # Format: {"Playlist Name": {"tracks": [], "image_path": None, "surface": None, "description": ""}}
liked_songs_custom_cover = {"image_path": None, "surface": None}
selected_custom_playlist_name = None
is_browsing_for_cover = False
browsing_cover_target = "create" # "create", "custom_view", or "liked_view"

# --- NEW GUI INPUT STATES ---
show_create_playlist_modal = False
playlist_input_text = ""
playlist_desc_text = ""
active_input_field = "name" # "name" or "description"
show_add_to_playlist_modal = False
track_to_add_to_playlist = None
modal_playlist_cover_surface = None  
modal_playlist_cover_path = None

# Marquee Description Animation Setup
marquee_offset = 0.0
marquee_direction = 1

# Browser, Search, Library & Touch Engine States
is_browsing_storage = False
search_input_active = False
search_query = ""
viewing_liked_playlist = False
playlist_is_playing = False  
viewing_settings_page = False

is_dragging_grid = False
last_touch_y = 0
total_drag_dy = 0

# --- SMOOTH SCROLLING TARGET ENGINE ---
music_grid_scroll_offset = 0.0  
target_music_scroll = 0.0
browser_scroll_offset = 0       
target_browser_scroll = 0.0     
settings_scroll_offset = 0
target_settings_scroll = 0.0
max_music_scroll = 0
max_browser_scroll = 0
max_settings_scroll = 0

ROOT_PATH = "/storage/emulated/0" if os.path.exists("/storage/emulated/0") else "/sdcard"
current_browser_path = ROOT_PATH
browser_items = []  

search_message = "Tap '+ Add Folder' to open the built-in storage browser."

# Global interaction boundaries
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
star_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_play_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_random_btn_rect = pygame.Rect(0, 0, 0, 0) # Track boundary for new playlist header shuffle trigger
add_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
settings_btn_rect = pygame.Rect(0, 0, 0, 0)
create_playlist_btn_rect = pygame.Rect(0, 0, 0, 0)
select_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
cancel_browser_btn_rect = pygame.Rect(0, 0, 0, 0)
close_settings_btn_rect = pygame.Rect(0, 0, 0, 0)
progress_bar_rect = pygame.Rect(0, 0, 0, 0)

# Modal Interaction Buttons
modal_close_rect = pygame.Rect(0, 0, 0, 0)
modal_save_rect = pygame.Rect(0, 0, 0, 0)
modal_input_rect = pygame.Rect(0, 0, 0, 0)
modal_desc_rect = pygame.Rect(0, 0, 0, 0)
modal_image_picker_rect = pygame.Rect(0, 0, 0, 0)

# --- PLAYLIST AUTO-ADVANCE & NAVIGATION TRACKING ENGINE ---
def advance_track(backward=False):
    global current_track, is_playing
    if viewing_liked_playlist and playlist_is_playing:
        playlist = liked_tracks
    elif selected_custom_playlist_name and playlist_is_playing:
        playlist = custom_playlists[selected_custom_playlist_name]["tracks"]
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
        # Integrated Shuffle Player Routine Strategy
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
        is_playing = True
        load_and_play_track(current_track["path"])

# --- HYBRID PLAYBACK ENGINE CORE ---
def load_and_play_track(track_path):
    global track_duration, track_start_accumulator, TEMP_WAV_PATH, current_backend, music_loaded
    
    music_loaded = False
    try: pygame.mixer.music.stop()
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
        except Exception as e:
            print(f"Playback engine error: {e}")
            music_loaded = False

# --- DIRECTORY NAVIGATION LOGIC ---
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

# --- UI DRAWING FUNCTIONS ---

def get_virtual_mouse_pos():
    real_x, real_y = pygame.mouse.get_pos()
    virtual_x = int(real_x * (WIDTH / REAL_WIDTH))
    virtual_y = int(real_y * (HEIGHT / REAL_HEIGHT))
    return (virtual_x, virtual_y)

def draw_manual_thumbs_up(surface, x, y, w, h, color):
    pygame.draw.rect(surface, color, (x, y + h * 0.5, w * 0.22, h * 0.4), border_radius=max(1, int(w * 0.04)))
    pygame.draw.rect(surface, color, (x + w * 0.28, y + h * 0.35, w * 0.62, h * 0.55), border_radius=max(1, int(w * 0.06)))
    pygame.draw.rect(surface, color, (x + w * 0.28, y, w * 0.25, h * 0.45), border_radius=max(1, int(w * 0.06)))

def draw_spotify_shuffle_icon(surface, rect, color):
    """Draws a vector style crossing shuffle icon matching Spotify's layout"""
    cx, cy = rect.centerx, rect.centery
    w, h = 16, 12
    x_left = cx - w // 2
    x_right = cx + w // 2
    y_top = cy - h // 2
    y_bottom = cy + h // 2
    
    # Top strand going to bottom right
    pygame.draw.line(surface, color, (x_left, y_top), (cx - 2, y_top), 2)
    pygame.draw.line(surface, color, (cx - 2, y_top), (cx + 2, y_bottom), 2)
    pygame.draw.line(surface, color, (cx + 2, y_bottom), (x_right, y_bottom), 2)
    
    # Bottom strand going to top right
    pygame.draw.line(surface, color, (x_left, y_bottom), (cx - 2, y_bottom), 2)
    pygame.draw.line(surface, color, (cx - 2, y_bottom), (cx + 2, y_top), 2)
    pygame.draw.line(surface, color, (cx + 2, y_top), (x_right, y_top), 2)
    
    # Arrows on right heads
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

def get_wrapped_lines(text, font, max_width):
    """Splits text into multiple lines by words OR individual characters if no spaces exist"""
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
    """Draws an aesthetic, flat transparent overlay bar at the bottom matching the frame format"""
    if rect.collidepoint(mouse_pos):
        overlay_height = 32
        overlay_surf = pygame.Surface((rect.width, overlay_height), pygame.SRCALPHA)
        # Transparent solid dark overlay bar matching exactly the frame width
        overlay_surf.fill((0, 0, 0, 180))
        
        hint_surf = font_small.render("Choose Cover Image", True, COLOR_WHITE)
        tx = (rect.width - hint_surf.get_width()) // 2
        ty = (overlay_height - hint_surf.get_height()) // 2
        overlay_surf.blit(hint_surf, (tx, ty))
        
        surface.blit(overlay_surf, (rect.x, rect.bottom - overlay_height))

def draw_sidebar():
    global sidebar_rects
    sidebar_rects = [] 
    
    content_bottom_margin = 90 if current_track["title"] != "Select a song" else 0
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
        elif is_hovered or (current_page == item and not is_browsing_storage and not viewing_liked_playlist and not viewing_settings_page and not selected_custom_playlist_name and not show_create_playlist_modal and not show_add_to_playlist_modal):
            pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=5)
            text_color = COLOR_WHITE
        else:
            text_color = COLOR_TEXT_MUTED
            
        text_surf = font_body.render(item, True, text_color)
        virtual_surface.blit(text_surf, (25, y_offset))
        y_offset += 40

def draw_main_content():
    global track_rects, add_folder_btn_rect, settings_btn_rect, create_playlist_btn_rect, browser_rects, settings_dir_rects, custom_playlist_rects, select_folder_btn_rect, cancel_browser_btn_rect, close_settings_btn_rect, liked_songs_card_rect, playlist_play_btn_rect, playlist_random_btn_rect, playlist_cover_rect, max_music_scroll, max_browser_scroll, max_settings_scroll, marquee_offset, marquee_direction
    track_rects = []
    browser_rects = []
    settings_dir_rects = []
    custom_playlist_rects = []
    
    content_bottom_margin = 90 if current_track["title"] != "Select a song" else 0
    main_rect = pygame.Rect(230, 0, WIDTH - 230, HEIGHT - content_bottom_margin)
    pygame.draw.rect(virtual_surface, COLOR_BLACK, main_rect)
    mouse_pos = get_virtual_mouse_pos()

    # Early intercept when full page destination selection view is open
    if show_add_to_playlist_modal:
        return

    # --- DETAILED PLAYLIST VIEWS (LIKED OR CUSTOM) ---
    if (viewing_liked_playlist or selected_custom_playlist_name) and current_page == "Your Library" and not is_browsing_for_cover:
        is_custom = selected_custom_playlist_name is not None
        active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if is_custom else liked_tracks
        p_title_text = selected_custom_playlist_name if is_custom else "Liked Songs"
        
        header_rect = pygame.Rect(230, 0, WIDTH - 230, 200)
        pygame.draw.rect(virtual_surface, COLOR_HOVER, header_rect)
        
        playlist_cover_rect = pygame.Rect(260, 30, 140, 140)
        
        if is_custom and custom_playlists[selected_custom_playlist_name]["surface"]:
            disp_surf = pygame.transform.smoothscale(custom_playlists[selected_custom_playlist_name]["surface"], (140, 140))
            virtual_surface.blit(disp_surf, (260, 30))
        elif not is_custom and liked_songs_custom_cover["surface"]:
            disp_surf = pygame.transform.smoothscale(liked_songs_custom_cover["surface"], (140, 140))
            virtual_surface.blit(disp_surf, (260, 30))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, playlist_cover_rect)
            if not is_custom:
                draw_manual_thumbs_up(virtual_surface, 305, 75, 50, 50, COLOR_BLACK)
            else:
                draw_spotify_pencil(virtual_surface, 330, 100, COLOR_BLACK)
                
        # Aesthetic, sharp matching overlay layout across all frames
        draw_unified_cover_overlay(virtual_surface, playlist_cover_rect, mouse_pos)
        
        type_lbl = font_small.render("CUSTOM PLAYLIST" if is_custom else "PUBLIC PLAYLIST", True, COLOR_WHITE)
        playlist_title = font_huge.render(p_title_text, True, COLOR_WHITE)
        
        virtual_surface.blit(type_lbl, (420, 45))
        virtual_surface.blit(playlist_title, (420, 70))

        # Render Playlist Description Layout Panel
        if is_custom:
            desc_str = custom_playlists[selected_custom_playlist_name].get("description", "")
            base_meta_str = f" • {len(active_tracks)} songs"
            
            if desc_str:
                desc_w = font_body.size(desc_str)[0]
                meta_w = font_body.size(base_meta_str)[0]
                max_allowed_w = WIDTH - 440 - meta_w
                
                if desc_w > max_allowed_w:
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
                    virtual_surface.blit(marquee_surf, (420, 140))
                    
                    meta_lbl = font_body.render(base_meta_str, True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(meta_lbl, (420 + max_allowed_w, 140))
                else:
                    info_lbl = font_body.render(f"{desc_str}{base_meta_str}", True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(info_lbl, (420, 140))
            else:
                info_lbl = font_body.render(f"Local Account{base_meta_str}", True, COLOR_TEXT_MUTED)
                virtual_surface.blit(info_lbl, (420, 140))
        else:
            info_lbl = font_body.render(f"Local Account • {len(active_tracks)} songs", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(info_lbl, (420, 140))
        
        # PLAYLIST CONTROLS: Play/Pause Button
        playlist_play_btn_rect = pygame.Rect(260, 215, 50, 50)
        is_p_hovered = playlist_play_btn_rect.collidepoint(mouse_pos)
        is_p_clicked = is_p_hovered and pygame.mouse.get_pressed()[0]
        
        if is_p_clicked:
            pygame.draw.circle(virtual_surface, (20, 150, 65), (285, 240), 23)
        elif is_p_hovered:
            pygame.draw.circle(virtual_surface, (40, 230, 110), (285, 240), 26)
        else:
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (285, 240), 25)
            
        if not (is_playing and playlist_is_playing):
            pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(280, 230), (280, 250), (295, 240)])
        else:
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (279, 232, 4, 16))
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (287, 232, 4, 16))

        # PLAYLIST CONTROLS: Added Random Button adjacent to Play button
        playlist_random_btn_rect = pygame.Rect(325, 222, 36, 36)
        is_pr_hovered = playlist_random_btn_rect.collidepoint(mouse_pos)
        
        if is_pr_hovered:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, playlist_random_btn_rect.center, 18)
            shuffle_icon_color = COLOR_WHITE
        else:
            shuffle_icon_color = COLOR_TEXT_MUTED
        draw_spotify_shuffle_icon(virtual_surface, playlist_random_btn_rect, shuffle_icon_color)
            
        hash_lbl = font_small.render("#  TITLE", True, COLOR_TEXT_MUTED)
        album_lbl = font_small.render("ALBUM", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(hash_lbl, (270, 285))
        virtual_surface.blit(album_lbl, (650, 285))
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 305), (WIDTH - 40, 305), 1)
        
        total_content_height = len(active_tracks) * 50
        max_music_scroll = max(0, total_content_height - (HEIGHT - 315 - content_bottom_margin) + 50)
        
        clip_rect = pygame.Rect(230, 315, WIDTH - 230, HEIGHT - 315 - content_bottom_margin)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 315 - int(music_grid_scroll_offset)
        for index, track in enumerate(active_tracks):
            row_rect = pygame.Rect(250, y_offset, WIDTH - 280, 45)
            if row_rect.colliderect(clip_rect):
                track_rects.append((row_rect, track))
                
                is_row_hovered = row_rect.collidepoint(mouse_pos)
                is_row_clicked = is_row_hovered and pygame.mouse.get_pressed()[0]
                
                if is_row_clicked:
                    pygame.draw.rect(virtual_surface, (60, 60, 60), row_rect, border_radius=6)
                elif track["path"] in green_toggled_tracks:
                    # Renders row background green if toggled active
                    pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, row_rect, border_radius=6)
                elif is_row_hovered:
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, row_rect, border_radius=6)
                
                if track["path"] in green_toggled_tracks:
                    title_color = COLOR_BLACK
                else:
                    title_color = COLOR_SPOTIFY_GREEN if track["title"] == current_track["title"] else COLOR_WHITE
                
                num_surf = font_body.render(str(index + 1), True, COLOR_BLACK if track["path"] in green_toggled_tracks else COLOR_TEXT_MUTED)
                title_surf = font_body.render(track["title"], True, title_color)
                artist_surf = font_small.render(track["artist"], True, COLOR_BLACK if track["path"] in green_toggled_tracks else COLOR_TEXT_MUTED)
                album_surf = font_body.render(track["album"], True, COLOR_BLACK if track["path"] in green_toggled_tracks else COLOR_TEXT_MUTED)
                
                virtual_surface.blit(num_surf, (270, y_offset + 12))
                virtual_surface.blit(title_surf, (310, y_offset + 4))
                virtual_surface.blit(artist_surf, (310, y_offset + 24))
                virtual_surface.blit(album_surf, (650, y_offset + 12))
                
            y_offset += 50
            
        virtual_surface.set_clip(None)

    # --- STORAGE BROWSER / CUSTOM COVER FILE EXPLORER VIEW ---
    elif (is_browsing_storage or is_browsing_for_cover) and current_page in ["Search", "Your Library"]:
        title_string = "Import custom cover picture (.png, .jpg)" if is_browsing_for_cover else "Device Storage Explorer"
        browser_title = font_title.render(title_string, True, COLOR_WHITE)
        virtual_surface.blit(browser_title, (260, 40))
        
        path_lbl = font_small.render(f"Path: {current_browser_path}", True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(path_lbl, (260, 75))
        
        select_folder_btn_rect = pygame.Rect(730, 35, 160, 35)
        cancel_browser_btn_rect = pygame.Rect(900, 35, 100, 35)
        
        sf_hovered = select_folder_btn_rect.collidepoint(mouse_pos)
        sf_clicked = sf_hovered and pygame.mouse.get_pressed()[0]
        if sf_clicked:
            sf_color = (20, 150, 65)
        else:
            sf_color = COLOR_SPOTIFY_GREEN if sf_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, sf_color, select_folder_btn_rect, border_radius=15)
        
        sf_text = "✓ Confirm File" if is_browsing_for_cover else "✓ Select Current"
        sf_lbl = font_small.render(sf_text, True, COLOR_WHITE if sf_color == COLOR_LIGHT_GREY else COLOR_BLACK)
        virtual_surface.blit(sf_lbl, (755, 44))
        
        cc_hovered = cancel_browser_btn_rect.collidepoint(mouse_pos)
        cc_clicked = cc_hovered and pygame.mouse.get_pressed()[0]
        if cc_clicked:
            cc_color = (30, 30, 30)
        else:
            cc_color = COLOR_HOVER if cc_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, cc_color, cancel_browser_btn_rect, border_radius=15)
        cc_lbl = font_small.render("Cancel", True, COLOR_WHITE)
        virtual_surface.blit(cc_lbl, (930, 44))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 115), (WIDTH - 40, 115), 1)
        
        total_content_height = len(browser_items) * 42
        max_browser_scroll = max(0, total_content_height - (HEIGHT - 130 - content_bottom_margin) + 30)
        
        clip_rect = pygame.Rect(230, 130, WIDTH - 230, HEIGHT - 130 - content_bottom_margin)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 130 - int(browser_scroll_offset)
        for item in browser_items:
            item_row_rect = pygame.Rect(250, y_offset - 4, WIDTH - 280, 35)
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
                virtual_surface.blit(item_surf, (260, y_offset))
            y_offset += 42
            
        virtual_surface.set_clip(None)

    # --- DEDICATED SETTINGS PAGE VIEW ---
    elif viewing_settings_page and current_page == "Search":
        settings_title = font_title.render("Imported Music Directories", True, COLOR_WHITE)
        virtual_surface.blit(settings_title, (260, 40))
        
        close_settings_btn_rect = pygame.Rect(900, 35, 100, 35)
        cs_hovered = close_settings_btn_rect.collidepoint(mouse_pos)
        cs_clicked = cs_hovered and pygame.mouse.get_pressed()[0]
        if cs_clicked:
            cs_color = (30, 30, 30)
        else:
            cs_color = COLOR_HOVER if cs_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, cs_color, close_settings_btn_rect, border_radius=15)
        cs_lbl = font_small.render("Back", True, COLOR_WHITE)
        virtual_surface.blit(cs_lbl, (936, 44))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 115), (WIDTH - 40, 115), 1)
        
        total_content_height = len(saved_directories) * 50
        max_settings_scroll = max(0, total_content_height - (HEIGHT - 130 - content_bottom_margin) + 30)
        
        clip_rect = pygame.Rect(230, 130, WIDTH - 230, HEIGHT - 130 - content_bottom_margin)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 130 - int(settings_scroll_offset)
        for d_path in saved_directories:
            row_item_rect = pygame.Rect(250, y_offset - 4, WIDTH - 280, 42)
            if row_item_rect.colliderect(clip_rect):
                settings_dir_rects.append((row_item_rect, d_path))
                
                is_row_h = row_item_rect.collidepoint(mouse_pos)
                row_bg = COLOR_RED if is_row_h else COLOR_LIGHT_GREY
                pygame.draw.rect(virtual_surface, row_bg, row_item_rect, border_radius=6)
                
                lbl_path = font_body.render(f"  [FOLDER]  {d_path}", True, COLOR_WHITE)
                lbl_del = font_body.render("Delete and Clear Music  [x] ", True, COLOR_WHITE if is_row_h else COLOR_TEXT_MUTED)
                
                virtual_surface.blit(lbl_path, (265, y_offset + 6))
                virtual_surface.blit(lbl_del, (WIDTH - 250, y_offset + 6))
            y_offset += 50
            
        virtual_surface.set_clip(None)

    # --- SEARCH PAGE ---
    elif current_page == "Search":
        search_title = font_title.render("Search Results", True, COLOR_WHITE)
        virtual_surface.blit(search_title, (260, 40))
        
        add_folder_btn_rect = pygame.Rect(780, 80, 150, 40)
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
        virtual_surface.blit(btn_txt, (818, 92))

        if saved_directories:
            settings_btn_rect = pygame.Rect(945, 80, 40, 40)
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

        pygame.draw.rect(virtual_surface, COLOR_WHITE, search_box_rect, border_radius=20)
        if search_input_active and not show_create_playlist_modal:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, search_box_rect, width=2, border_radius=20)
            
        if search_query != "":
            search_text = font_small.render(f"  {search_query}", True, COLOR_BLACK)
        else:
            search_text = font_small.render(f"  {search_message}", True, COLOR_LIGHT_GREY)
        virtual_surface.blit(search_text, (275, 92))

        filtered_tracks = []
        cleaned_query = search_query.strip().lower()
        for track in imported_tracks:
            if cleaned_query == "" or cleaned_query in track["raw_title"].lower() or cleaned_query in track["album"].lower():
                filtered_tracks.append(track)

        if not imported_tracks:
            empty_surf = font_body.render("No local music loaded. Tap '+ Add Folder' above to explore your storage!", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_surf, (260, 160))
        elif not filtered_tracks:
            no_match_surf = font_body.render(f"No results match your search query for '{search_query}'.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(no_match_surf, (260, 160))
        else:
            start_x = 260
            start_y = 150
            card_width = 140
            card_height = 140
            gap_x = 14  
            gap_y = 55  
            
            cols = (WIDTH - start_x - 20) // (card_width + gap_x)
            rows = (len(filtered_tracks) + cols - 1) // cols if cols > 0 else 0
            total_content_height = rows * (card_height + gap_y)
            max_music_scroll = max(0, total_content_height - (HEIGHT - 140 - content_bottom_margin) + 50)
            
            clip_rect = pygame.Rect(230, 140, WIDTH - 230, HEIGHT - 140 - content_bottom_margin)
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
                    elif track["path"] in green_toggled_tracks:
                        # Renders background card frame green if toggled active
                        pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, card_rect, border_radius=8)
                    elif is_card_hovered:
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, card_rect, border_radius=8)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_CARD_BG, card_rect, border_radius=8)
                    
                    cover_rect = pygame.Rect(box_x + 12, box_y + 12, card_width - 24, card_height - 24)
                    if track["path"] in green_toggled_tracks:
                        cover_color = COLOR_WHITE
                    else:
                        cover_color = COLOR_SPOTIFY_GREEN if track["title"] == current_track["title"] else COLOR_LIGHT_GREY
                    pygame.draw.rect(virtual_surface, cover_color, cover_rect, border_radius=6)
                    
                    if track["path"] in green_toggled_tracks:
                        title_color = COLOR_BLACK
                        sub_color = COLOR_BLACK
                    else:
                        title_color = COLOR_SPOTIFY_GREEN if track["title"] == current_track["title"] else COLOR_WHITE
                        sub_color = COLOR_TEXT_MUTED
                        
                    title_surf = font_small.render(track["title"], True, title_color)
                    virtual_surface.blit(title_surf, (box_x + 12, box_y + card_height - 4))
                    
                    sub_surf = font_small.render(track["album"], True, sub_color)
                    virtual_surface.blit(sub_surf, (box_x + 12, box_y + card_height + 14))

            virtual_surface.set_clip(None)

    # --- YOUR LIBRARY GRID VIEW ---
    elif current_page == "Your Library":
        lib_title = font_title.render("Your Library", True, COLOR_WHITE)
        virtual_surface.blit(lib_title, (260, 40))
        
        create_playlist_btn_rect = pygame.Rect(390, 35, 40, 40)
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
        
        liked_songs_card_rect = pygame.Rect(260, 95, 160, 200)
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
            virtual_surface.blit(disp_thumb, (275, 110))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, (275, 110, 130, 110), border_radius=4)
            draw_manual_thumbs_up(virtual_surface, 315, 140, 50, 50, COLOR_BLACK)
        
        card_txt1 = font_body.render("Liked Songs", True, COLOR_WHITE)
        card_txt2 = font_small.render(f"Playlist • {len(liked_tracks)} songs", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(card_txt1, (275, 230))
        virtual_surface.blit(card_txt2, (275, 255))

        start_x = 260
        start_y = 95
        card_w, card_h = 160, 200
        gap_x, gap_y = 20, 20
        columns_count = (WIDTH - start_x - 20) // (card_w + gap_x)
        
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

# --- NEW GUI DIALOG POPUP RENDERING ENGINE ---
def draw_modals():
    global modal_close_rect, modal_save_rect, modal_input_rect, modal_desc_rect, modal_playlist_rects, modal_image_picker_rect, max_music_scroll
    mouse_pos = get_virtual_mouse_pos()
    
    # Modal A: Full-Page Create Playlist Interface
    if show_create_playlist_modal:
        if is_browsing_for_cover:
            draw_main_content()
            return

        pygame.draw.rect(virtual_surface, COLOR_BLACK, (230, 0, WIDTH - 230, HEIGHT))
        
        lbl = font_huge.render("Create playlist", True, COLOR_WHITE)
        virtual_surface.blit(lbl, (280, 60))
        
        modal_image_picker_rect = pygame.Rect(280, 160, 220, 220)
        if modal_playlist_cover_surface:
            disp_modal_cover = pygame.transform.smoothscale(modal_playlist_cover_surface, (220, 220))
            virtual_surface.blit(disp_modal_cover, (280, 160))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_image_picker_rect)
            draw_spotify_pencil(virtual_surface, 390, 270, COLOR_BLACK)
            
        # Outer cover overlay applied seamlessly across everything
        draw_unified_cover_overlay(virtual_surface, modal_image_picker_rect, mouse_pos)
            
        # --- PLAYLIST NAME INPUT ---
        label_meta = font_small.render("Name", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(label_meta, (530, 160))
        
        modal_input_rect = pygame.Rect(530, 185, 450, 42)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, modal_input_rect, border_radius=6)
        if search_input_active and active_input_field == "name":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_input_rect, width=2, border_radius=6)
            
        if playlist_input_text:
            text_surf = font_body.render(playlist_input_text, True, COLOR_WHITE)
        else:
            text_surf = font_body.render("My Playlist #1", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(text_surf, (modal_input_rect.x + 15, modal_input_rect.y + 11))
        
        # --- PLAYLIST DESCRIPTION MULTI-LINE AUTO-WRAP INPUT ---
        label_desc = font_small.render("Description", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(label_desc, (530, 245))
        
        modal_desc_rect = pygame.Rect(530, 270, 450, 110)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, modal_desc_rect, border_radius=6)
        if search_input_active and active_input_field == "description":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_desc_rect, width=2, border_radius=6)
            
        if playlist_desc_text:
            wrapped_lines = get_wrapped_lines(playlist_desc_text, font_small, 420)
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
        virtual_surface.blit(desc_lbl, (280, 415))
        
        modal_close_rect = pygame.Rect(760, 405, 100, 42)
        modal_save_rect = pygame.Rect(880, 405, 100, 42)
        
        c_bg = COLOR_HOVER if modal_close_rect.collidepoint(mouse_pos) else COLOR_CARD_BG
        pygame.draw.rect(virtual_surface, c_bg, modal_close_rect, border_radius=21)
        c_txt = font_body.render("Cancel", True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (modal_close_rect.x + 24, modal_close_rect.y + 11))
        
        s_bg = (40, 230, 110) if modal_save_rect.collidepoint(mouse_pos) else COLOR_SPOTIFY_GREEN
        pygame.draw.rect(virtual_surface, s_bg, modal_save_rect, border_radius=21)
        s_txt = font_body.render("Save", True, COLOR_BLACK)
        virtual_surface.blit(s_txt, (modal_save_rect.x + 32, modal_save_rect.y + 11))

    # Modal B: Full Page Playlist Destination Selector Screen (Excludes Favorites)
    elif show_add_to_playlist_modal:
        content_bottom_margin = 90 if current_track["title"] != "Select a song" else 0
        
        # Draw full page layout area next to the sidebar panel layout boundary
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (230, 0, WIDTH - 230, HEIGHT - content_bottom_margin))
        
        # Heading panel configuration
        lbl = font_title.render("Pick a playlist to add it to", True, COLOR_WHITE)
        virtual_surface.blit(lbl, (260, 40))
        
        track_lbl_text = f"Song: {track_to_add_to_playlist['title']}" if track_to_add_to_playlist else ""
        track_lbl = font_small.render(track_lbl_text, True, COLOR_TEXT_MUTED)
        virtual_surface.blit(track_lbl, (260, 70))
        
        modal_close_rect = pygame.Rect(900, 35, 100, 35)
        c_bg = COLOR_HOVER if modal_close_rect.collidepoint(mouse_pos) else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, c_bg, modal_close_rect, border_radius=15)
        c_txt = font_small.render("Cancel", True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (modal_close_rect.x + 28, modal_close_rect.y + 8))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 115), (WIDTH - 40, 115), 1)
        
        modal_playlist_rects = []
        p_names = list(custom_playlists.keys())
        
        if not p_names:
            empty_lbl = font_body.render("No custom playlists built yet.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_lbl, (260, 150))
            hint_lbl = font_small.render("Go to 'Your Library' and tap '+' to create one.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(hint_lbl, (260, 180))
            max_music_scroll = 0
        else:
            total_content_height = len(p_names) * 55
            max_music_scroll = max(0, total_content_height - (HEIGHT - 130 - content_bottom_margin) + 30)
            
            clip_rect = pygame.Rect(230, 130, WIDTH - 230, HEIGHT - 130 - content_bottom_margin)
            virtual_surface.set_clip(clip_rect)
            
            y_item = 130 - int(music_grid_scroll_offset)
            for p_name in p_names:
                item_rect = pygame.Rect(250, y_item, WIDTH - 280, 45)
                if item_rect.colliderect(clip_rect):
                    modal_playlist_rects.append((item_rect, p_name))
                    
                    if item_rect.collidepoint(mouse_pos):
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=6)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, item_rect, border_radius=6)
                        
                    p_lbl = font_body.render(f" ♫  {p_name}", True, COLOR_WHITE)
                    virtual_surface.blit(p_lbl, (item_rect.x + 15, item_rect.y + 12))
                    
                    count_lbl = font_small.render(f"{len(custom_playlists[p_name]['tracks'])} tracks", True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(count_lbl, (WIDTH - 140, item_rect.y + 14))
                y_item += 55
                
            virtual_surface.set_clip(None)

def draw_media_bar():
    global play_btn_rect, prev_btn_rect, next_btn_rect, minus_10_btn_rect, plus_10_btn_rect, mediabar_add_btn_rect, star_btn_rect, shuffle_btn_rect, progress_bar_rect
    
    if current_track["title"] == "Select a song":
        return

    bar_rect = pygame.Rect(0, HEIGHT - 90, WIDTH, 90)
    pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, bar_rect)
    
    now_playing_title = font_body.render(current_track["title"], True, COLOR_WHITE)
    now_playing_artist = font_small.render(current_track["artist"], True, COLOR_TEXT_MUTED)
    virtual_surface.blit(now_playing_title, (20, HEIGHT - 65))
    virtual_surface.blit(now_playing_artist, (20, HEIGHT - 45))
    
    center_x = WIDTH // 2
    center_y = HEIGHT - 60
    
    star_btn_rect = pygame.Rect(center_x - 125, center_y - 10, 20, 20)
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

    # --- RECONFIGURED CONFIGURATION ROW CONTROL SLOTS ---
    # Moved Add Folder Plus button between Thumbs-Up and -10s
    mediabar_add_btn_rect = pygame.Rect(center_x - 95, center_y - 14, 28, 28)
    minus_10_btn_rect     = pygame.Rect(center_x - 55, center_y - 16, 32, 32)
    prev_btn_rect         = pygame.Rect(center_x - 18, center_y - 18, 28, 36)
    play_btn_rect         = pygame.Rect(center_x + 15, center_y - 18, 36, 36)
    next_btn_rect         = pygame.Rect(center_x + 56, center_y - 18, 28, 36)
    plus_10_btn_rect      = pygame.Rect(center_x + 90, center_y - 16, 32, 32)
    # Shuffle sitting exactly next to +10s on the right wing boundary
    shuffle_btn_rect      = pygame.Rect(center_x + 132, center_y - 16, 32, 32)

    # --- RENDER PLAYLIST QUICK ADD BUTTON (CIRCLE PLUS BETWEEN THUMBS UP & -10) ---
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

    # --- RENDER -10S BUTTON ---
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

    # --- RENDER PREVIOUS BUTTON ---
    prev_hover = prev_btn_rect.collidepoint(mouse_pos)
    prev_click = prev_hover and pygame.mouse.get_pressed()[0]
    prev_color = COLOR_SPOTIFY_GREEN if prev_click else (COLOR_WHITE if prev_hover else COLOR_TEXT_MUTED)
    pygame.draw.polygon(virtual_surface, prev_color, [(center_x - 15, center_y), (center_x, center_y - 9), (center_x, center_y + 9)])
    
    # --- RENDER MAIN PLAY CONTROL BUTTON ---
    is_mb_play_hovered = play_btn_rect.collidepoint(mouse_pos)
    is_mb_play_clicked = is_mb_play_hovered and pygame.mouse.get_pressed()[0]
    
    if is_mb_play_clicked:
        pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, (center_x + 33, center_y), 16)
    elif is_mb_play_hovered:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, (center_x + 33, center_y), 20)
    else:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, (center_x + 33, center_y), 18)
    
    if not is_playing:
        pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(center_x + 30, center_y - 6), (center_x + 30, center_y + 6), (center_x + 40, center_y)])
    else:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (center_x + 29, center_y - 6, 3, 12))
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (center_x + 35, center_y - 6, 3, 12))

    # --- RENDER NEXT BUTTON ---
    next_hover = next_btn_rect.collidepoint(mouse_pos)
    next_click = next_hover and pygame.mouse.get_pressed()[0]
    next_color = COLOR_SPOTIFY_GREEN if next_click else (COLOR_WHITE if next_hover else COLOR_TEXT_MUTED)
    pygame.draw.polygon(virtual_surface, next_color, [(center_x + 80, center_y), (center_x + 65, center_y - 9), (center_x + 65, center_y + 9)])
    
    # --- RENDER +10S BUTTON ---
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

    # --- RENDER SHUFFLE RANDOM BUTTON (SPOTIFY SHUFFLE CLONE DESIGN) ---
    sh_hover = shuffle_btn_rect.collidepoint(mouse_pos)
    
    if is_shuffle:
        sh_icon_color = COLOR_SPOTIFY_GREEN
        # Draw small green active dot indicator under icon matching Spotify standard interface rules
        pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (shuffle_btn_rect.centerx, shuffle_btn_rect.centery + 12), 2)
    else:
        sh_icon_color = COLOR_WHITE if sh_hover else COLOR_TEXT_MUTED

    draw_spotify_shuffle_icon(virtual_surface, shuffle_btn_rect, sh_icon_color)

    progress_bar_width = 400
    progress_bar_x = center_x - (progress_bar_width // 2) + 20
    progress_bar_y = HEIGHT - 25
    progress_bar_rect = pygame.Rect(progress_bar_x, progress_bar_y - 10, progress_bar_width, 24)
    
    elapsed_sec = 0.0
    remaining_sec = 0.0
    percent_fill = 0.0
    
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

# --- MAIN LOOP ---
running = True

try: pygame.key.start_text_input()
except: pass

while running:
    dt = min(0.1, clock.get_time() / 1000.0)
    
    music_grid_scroll_offset += (target_music_scroll - music_grid_scroll_offset) * (15.0 * dt)
    browser_scroll_offset += (target_browser_scroll - browser_scroll_offset) * (15.0 * dt)
    settings_scroll_offset += (target_settings_scroll - settings_scroll_offset) * (15.0 * dt)

    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
            
        elif event.type == pygame.KEYDOWN:
            if show_create_playlist_modal and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    if active_input_field == "name":
                        playlist_input_text = playlist_input_text[:-1]
                    else:
                        playlist_desc_text = playlist_desc_text[:-1]
                elif event.key == pygame.K_RETURN:
                    search_input_active = False
                else:
                    if event.unicode and event.unicode.isprintable():
                        if active_input_field == "name" and len(playlist_input_text) < 20:
                            playlist_input_text += event.unicode
                        elif active_input_field == "description":
                            lines_test = get_wrapped_lines(playlist_desc_text + event.unicode, font_small, 420)
                            if len(lines_test) * 18 <= 90:  
                                playlist_desc_text += event.unicode
            
            elif current_page == "Search" and not is_browsing_storage and not viewing_settings_page:
                if search_input_active:
                    if event.key == pygame.K_BACKSPACE:
                        search_query = search_query[:-1]
                    elif event.key == pygame.K_ESCAPE or event.key == pygame.K_RETURN:
                        search_input_active = False
                    else:
                        if len(search_query) < 25 and event.unicode and event.unicode.isprintable():
                            search_query += event.unicode
                        
        elif event.type == pygame.MOUSEBUTTONDOWN:
            mouse_pos = get_virtual_mouse_pos()
            
            if not show_create_playlist_modal:
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

            if event.button == 3 and current_page == "Search" and not is_browsing_storage and not viewing_settings_page and not (show_create_playlist_modal or show_add_to_playlist_modal):
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
            if is_dragging_grid:
                mouse_pos = get_virtual_mouse_pos()
                dy = last_touch_y - mouse_pos[1]
                total_drag_dy += abs(dy)
                
                if show_create_playlist_modal:
                    if is_browsing_for_cover:
                        target_browser_scroll += dy * 1.5
                        target_browser_scroll = max(0.0, min(max_browser_scroll, target_browser_scroll))
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
                is_dragging_grid = False
                
                if total_drag_dy < 15:
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
                                    break
                        continue

                    if current_page == "Search" and viewing_settings_page and saved_directories:
                        clicked_panel_item = False
                        for rect, d_path in settings_dir_rects:
                            if rect.collidepoint(mouse_pos):
                                saved_directories.remove(d_path)
                                rebuild_imported_tracks()
                                clicked_panel_item = True
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
                                        except Exception as image_err:
                                            print(f"Error importing cover layout graphics: {image_err}")
                                        is_browsing_for_cover = False
                                    break
                        continue

                    # --- PLAYLIST HEADER INTERACTION HANDLING ---
                    if (viewing_liked_playlist or selected_custom_playlist_name) and current_page == "Your Library":
                        if playlist_cover_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "custom_view" if selected_custom_playlist_name else "liked_view"
                            update_browser_contents()
                            continue
                            
                        # Playlist Header Play button interaction
                        if playlist_play_btn_rect.collidepoint(mouse_pos):
                            active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if selected_custom_playlist_name else liked_tracks
                            if active_tracks:
                                if current_track["path"] != active_tracks[0]["path"]:
                                    current_track = active_tracks[0]  
                                    playlist_is_playing = True  
                                    is_playing = True
                                    load_and_play_track(current_track["path"])
                                else:
                                    is_playing = not is_playing
                                    if is_playing:
                                        if current_backend == "android": android_media_player.start()
                                        else: pygame.mixer.music.unpause()
                                    else:
                                        if current_backend == "android": android_media_player.pause()
                                        else: pygame.mixer.music.pause()

                        # Playlist Header Random button interaction
                        if playlist_random_btn_rect.collidepoint(mouse_pos):
                            active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if selected_custom_playlist_name else liked_tracks
                            if active_tracks:
                                is_shuffle = True  # Enable shuffle engine state in media bar
                                playlist_is_playing = True
                                random_index = random.randint(0, len(active_tracks) - 1)
                                current_track = active_tracks[random_index]
                                is_playing = True
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
                                content_bottom_margin = 90 if current_track["title"] != "Select a song" else 0
                                if current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name):
                                    clip_rect_bounds = pygame.Rect(230, 315, WIDTH - 230, HEIGHT - 315 - content_bottom_margin)
                                else:
                                    clip_rect_bounds = pygame.Rect(230, 140, WIDTH - 230, HEIGHT - 140 - content_bottom_margin)
                                    
                                if clip_rect_bounds.collidepoint(mouse_pos) and rect.collidepoint(mouse_pos):
                                    # Toggle track to green state on click, back to grey if clicked again
                                    if track["path"] in green_toggled_tracks:
                                        green_toggled_tracks.remove(track["path"])
                                    else:
                                        green_toggled_tracks.add(track["path"])
                                        
                                    current_track = track
                                    playlist_is_playing = True if (viewing_liked_playlist or selected_custom_playlist_name) else False
                                    is_playing = True 
                                    load_and_play_track(current_track["path"])
                                    
                        if current_track["title"] != "Select a song":
                            if progress_bar_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                                relative_x = mouse_pos[0] - progress_bar_rect.x
                                fraction = min(1.0, max(0.0, relative_x / progress_bar_rect.width))
                                seek_target = fraction * track_duration
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

                            # --- PLAYLIST QUICK ADD BUTTON (CIRCLE PLUS BETWEEN THUMBS UP & -10) ---
                            if mediabar_add_btn_rect.collidepoint(mouse_pos):
                                track_to_add_to_playlist = current_track
                                show_add_to_playlist_modal = True
                                target_music_scroll = 0.0

                            # --- SKIP -10S BUTTON LOGIC ---
                            if minus_10_btn_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
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

                            # --- SKIP +10S BUTTON LOGIC ---
                            if plus_10_btn_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
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
                                
                            # --- SHUFFLE TOGGLE BUTTON CLICK INTERCEPT ---
                            if shuffle_btn_rect.collidepoint(mouse_pos):
                                is_shuffle = not is_shuffle

                            if star_btn_rect.collidepoint(mouse_pos):
                                if current_track in liked_tracks:
                                    liked_tracks.remove(current_track)
                                else:
                                    liked_tracks.append(current_track)
            
    if is_playing and track_duration > 0 and music_loaded:
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
    
    scaled_frame = pygame.transform.scale(virtual_surface, (REAL_WIDTH, REAL_HEIGHT))
    screen.blit(scaled_frame, (0, 0))
    
    pygame.display.flip()
    clock.tick(DEVICE_REFRESH_RATE)

if TEMP_WAV_PATH and os.path.exists(TEMP_WAV_PATH):
    try: os.remove(TEMP_WAV_PATH)
    except: pass

if HAS_ANDROID_MEDIA and android_media_player:
    try: android_media_player.release()
    except: pass

pygame.quit()
sys.exit()

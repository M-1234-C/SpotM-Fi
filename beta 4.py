import pygame
import sys
import os
import tempfile
import time

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

# Browser, Search, Library & Touch Engine States
is_browsing_storage = False
search_input_active = False
search_query = ""
viewing_liked_playlist = False
playlist_is_playing = False  

is_dragging_grid = False
last_touch_y = 0
total_drag_dy = 0

ROOT_PATH = "/storage/emulated/0" if os.path.exists("/storage/emulated/0") else "/sdcard"
current_browser_path = ROOT_PATH
browser_items = []  
browser_scroll_offset = 0
music_grid_scroll_offset = 0  
max_music_scroll = 0

search_message = "Tap '+ Add Folder' to open the built-in storage browser."

# Global interaction boundaries
track_rects = []
sidebar_rects = []
browser_rects = []
liked_songs_card_rect = pygame.Rect(260, 95, 160, 200)
search_box_rect = pygame.Rect(260, 80, 500, 40)
play_btn_rect = pygame.Rect(0, 0, 0, 0)
prev_btn_rect = pygame.Rect(0, 0, 0, 0)
next_btn_rect = pygame.Rect(0, 0, 0, 0)
star_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_play_btn_rect = pygame.Rect(0, 0, 0, 0)
add_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
select_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
cancel_browser_btn_rect = pygame.Rect(0, 0, 0, 0)
progress_bar_rect = pygame.Rect(0, 0, 0, 0)

# --- PLAYLIST AUTO-ADVANCE & NAVIGATION TRACKING ENGINE ---
def advance_track(backward=False):
    global current_track, is_playing
    playlist = liked_tracks if (viewing_liked_playlist and playlist_is_playing) else imported_tracks
    if not playlist:
        return
    
    current_index = -1
    for i, track in enumerate(playlist):
        if track["path"] == current_track["path"]:
            current_index = i
            break
            
    if current_index != -1:
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
    is_mp4 = track_path.lower().endswith(('.mp4', '.m4a'))

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
    global browser_items, search_message, browser_scroll_offset
    browser_items = []
    browser_scroll_offset = 0
    
    if current_browser_path != ROOT_PATH and current_browser_path != "/":
        browser_items.append({"name": "[.. Go Back to Previous Folder]", "is_dir": True, "path": os.path.dirname(current_browser_path)})
        
    try:
        for item in sorted(os.listdir(current_browser_path)):
            full_path = os.path.join(current_browser_path, item)
            is_dir = os.path.isdir(full_path)
            browser_items.append({"name": item, "is_dir": is_dir, "path": full_path})
    except Exception:
        search_message = "Access Denied: Restricted system folder or permission missing."

def scan_confirmed_directory(target_dir):
    global imported_tracks, search_message, is_browsing_storage, saved_directories, music_grid_scroll_offset
    
    if target_dir not in saved_directories:
        saved_directories.append(target_dir)
        
    imported_tracks = []
    track_counter = 1
    new_songs_found = 0
    music_grid_scroll_offset = 0
    
    for directory in saved_directories:
        try:
            for file in os.listdir(directory):
                if file.lower().endswith(('.mp3', '.mp4', '.m4a', '.wav', '.ogg', '.flac', '.mpe', '.mpeg')):
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
            
    search_message = f"Scanned folder! Found {new_songs_found} media files in layout index."
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
        elif is_hovered or (current_page == item and not is_browsing_storage and not viewing_liked_playlist):
            pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=5)
            text_color = COLOR_WHITE
        else:
            text_color = COLOR_TEXT_MUTED
            
        text_surf = font_body.render(item, True, text_color)
        virtual_surface.blit(text_surf, (25, y_offset))
        y_offset += 40

def draw_main_content():
    global track_rects, add_folder_btn_rect, browser_rects, select_folder_btn_rect, cancel_browser_btn_rect, liked_songs_card_rect, playlist_play_btn_rect, max_music_scroll
    track_rects = []
    browser_rects = []
    
    content_bottom_margin = 90 if current_track["title"] != "Select a song" else 0
    main_rect = pygame.Rect(230, 0, WIDTH - 230, HEIGHT - content_bottom_margin)
    pygame.draw.rect(virtual_surface, COLOR_BLACK, main_rect)
    mouse_pos = get_virtual_mouse_pos()

    # --- FULL DETAILED PLAYLIST VIEW ---
    if viewing_liked_playlist and current_page == "Your Library":
        header_rect = pygame.Rect(230, 0, WIDTH - 230, 200)
        pygame.draw.rect(virtual_surface, COLOR_HOVER, header_rect)
        
        cover_rect = pygame.Rect(260, 30, 140, 140)
        pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, cover_rect, border_radius=6)
        
        draw_manual_thumbs_up(virtual_surface, 305, 75, 50, 50, COLOR_BLACK)
        
        type_lbl = font_small.render("PUBLIC PLAYLIST", True, COLOR_WHITE)
        playlist_title = font_huge.render("Liked Songs", True, COLOR_WHITE)
        info_lbl = font_body.render(f"Local Account • {len(liked_tracks)} songs", True, COLOR_TEXT_MUTED)
        
        virtual_surface.blit(type_lbl, (420, 45))
        virtual_surface.blit(playlist_title, (420, 70))
        virtual_surface.blit(info_lbl, (420, 140))
        
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
            
        hash_lbl = font_small.render("#  TITLE", True, COLOR_TEXT_MUTED)
        album_lbl = font_small.render("ALBUM", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(hash_lbl, (270, 285))
        virtual_surface.blit(album_lbl, (650, 285))
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 305), (WIDTH - 40, 305), 1)
        
        total_content_height = len(liked_tracks) * 50
        max_music_scroll = max(0, total_content_height - (HEIGHT - 315 - content_bottom_margin) + 50)
        
        clip_rect = pygame.Rect(230, 315, WIDTH - 230, HEIGHT - 315 - content_bottom_margin)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 315 - music_grid_scroll_offset
        for index, track in enumerate(liked_tracks):
            row_rect = pygame.Rect(250, y_offset, WIDTH - 280, 45)
            if row_rect.colliderect(clip_rect):
                track_rects.append((row_rect, track))
                
                is_row_hovered = row_rect.collidepoint(mouse_pos)
                is_row_clicked = is_row_hovered and pygame.mouse.get_pressed()[0]
                
                if is_row_clicked:
                    pygame.draw.rect(virtual_surface, (60, 60, 60), row_rect, border_radius=6)
                elif is_row_hovered:
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, row_rect, border_radius=6)
                
                title_color = COLOR_SPOTIFY_GREEN if track["title"] == current_track["title"] else COLOR_WHITE
                
                num_surf = font_body.render(str(index + 1), True, COLOR_TEXT_MUTED)
                title_surf = font_body.render(track["title"], True, title_color)
                artist_surf = font_small.render(track["artist"], True, COLOR_TEXT_MUTED)
                album_surf = font_body.render(track["album"], True, COLOR_TEXT_MUTED)
                
                virtual_surface.blit(num_surf, (270, y_offset + 12))
                virtual_surface.blit(title_surf, (310, y_offset + 4))
                virtual_surface.blit(artist_surf, (310, y_offset + 24))
                virtual_surface.blit(album_surf, (650, y_offset + 12))
                
            y_offset += 50
            
        virtual_surface.set_clip(None)

    # --- STORAGE BROWSER VIEW ---
    elif is_browsing_storage and current_page == "Search":
        browser_title = font_title.render("Device Storage Explorer", True, COLOR_WHITE)
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
        sf_lbl = font_small.render("✓ Select Current", True, COLOR_WHITE if sf_color == COLOR_LIGHT_GREY else COLOR_BLACK)
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
        
        y_offset = 130
        max_visible_items = 11
        visible_items = browser_items[browser_scroll_offset : browser_scroll_offset + max_visible_items]
        
        for item in visible_items:
            item_row_rect = pygame.Rect(250, y_offset - 4, WIDTH - 280, 35)
            browser_rects.append((item_row_rect, item))
            
            is_b_hovered = item_row_rect.collidepoint(mouse_pos)
            is_b_clicked = is_b_hovered and pygame.mouse.get_pressed()[0]
            
            if is_b_clicked:
                pygame.draw.rect(virtual_surface, (60, 60, 60), item_row_rect, border_radius=5)
            elif is_b_hovered:
                pygame.draw.rect(virtual_surface, COLOR_HOVER, item_row_rect, border_radius=5)
                
            if item["is_dir"]:
                prefix = "[FOLDER] "
                display_color = COLOR_SPOTIFY_GREEN if "music" in item["name"].lower() else COLOR_TEXT_MUTED
            else:
                prefix = "[FILE] "
                display_color = COLOR_WHITE
            
            item_surf = font_body.render(f"{prefix}{item['name']}", True, display_color)
            virtual_surface.blit(item_surf, (260, y_offset))
            y_offset += 42

    # --- SEARCH PAGE ---
    elif current_page == "Search":
        search_title = font_title.render("Search Results", True, COLOR_WHITE)
        virtual_surface.blit(search_title, (260, 40))
        
        add_folder_btn_rect = pygame.Rect(780, 80, 180, 40)
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
        virtual_surface.blit(btn_txt, (830, 92))

        pygame.draw.rect(virtual_surface, COLOR_WHITE, search_box_rect, border_radius=20)
        if search_input_active:
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
                box_y = start_y + (row * (card_height + gap_y)) - music_grid_scroll_offset
                
                card_rect = pygame.Rect(box_x, box_y, card_width, card_height + 40)
                
                if card_rect.colliderect(clip_rect):
                    track_rects.append((card_rect, track))
                    
                    is_card_hovered = card_rect.collidepoint(mouse_pos)
                    is_card_clicked = is_card_hovered and pygame.mouse.get_pressed()[0]
                    
                    if is_card_clicked:
                        pygame.draw.rect(virtual_surface, (45, 45, 45), card_rect, border_radius=8)
                    elif is_card_hovered:
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, card_rect, border_radius=8)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_CARD_BG, card_rect, border_radius=8)
                    
                    cover_rect = pygame.Rect(box_x + 12, box_y + 12, card_width - 24, card_height - 24)
                    cover_color = COLOR_SPOTIFY_GREEN if track["title"] == current_track["title"] else COLOR_LIGHT_GREY
                    pygame.draw.rect(virtual_surface, cover_color, cover_rect, border_radius=6)
                    
                    title_color = COLOR_SPOTIFY_GREEN if track["title"] == current_track["title"] else COLOR_WHITE
                    title_surf = font_small.render(track["title"], True, title_color)
                    virtual_surface.blit(title_surf, (box_x + 12, box_y + card_height - 4))
                    
                    sub_surf = font_small.render(track["album"], True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(sub_surf, (box_x + 12, box_y + card_height + 14))

            virtual_surface.set_clip(None)

    elif current_page == "Your Library":
        lib_title = font_title.render("Your Library", True, COLOR_WHITE)
        virtual_surface.blit(lib_title, (260, 40))
        
        liked_songs_card_rect = pygame.Rect(260, 95, 160, 200)
        is_lib_hovered = liked_songs_card_rect.collidepoint(mouse_pos)
        is_lib_clicked = is_lib_hovered and pygame.mouse.get_pressed()[0]
        
        if is_lib_clicked:
            pygame.draw.rect(virtual_surface, (45, 45, 45), liked_songs_card_rect, border_radius=8)
        elif is_lib_hovered:
            pygame.draw.rect(virtual_surface, COLOR_HOVER, liked_songs_card_rect, border_radius=8)
        else:
            pygame.draw.rect(virtual_surface, COLOR_CARD_BG, liked_songs_card_rect, border_radius=8)
            
        pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, (275, 110, 130, 110), border_radius=4)
        
        draw_manual_thumbs_up(virtual_surface, 315, 140, 50, 50, COLOR_BLACK)
        
        card_txt1 = font_body.render("Liked Songs", True, COLOR_WHITE)
        card_txt2 = font_small.render(f"Playlist • {len(liked_tracks)} songs", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(card_txt1, (275, 230))
        virtual_surface.blit(card_txt2, (275, 255))

def draw_media_bar():
    global play_btn_rect, prev_btn_rect, next_btn_rect, star_btn_rect, progress_bar_rect
    
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
    
    star_btn_rect = pygame.Rect(center_x - 75, center_y - 10, 20, 20)
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

    play_btn_rect = pygame.Rect(center_x - 18, center_y - 18, 36, 36)
    is_mb_play_hovered = play_btn_rect.collidepoint(mouse_pos)
    is_mb_play_clicked = is_mb_play_hovered and pygame.mouse.get_pressed()[0]
    
    if is_mb_play_clicked:
        pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, (center_x, center_y), 16)
    elif is_mb_play_hovered:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, (center_x, center_y), 20)
    else:
        pygame.draw.circle(virtual_surface, COLOR_WHITE, (center_x, center_y), 18)
    
    if not is_playing:
        pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(center_x - 4, center_y - 6), (center_x - 4, center_y + 6), (center_x + 6, center_y)])
    else:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (center_x - 5, center_y - 6, 3, 12))
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (center_x + 2, center_y - 6, 3, 12))
    
    prev_btn_rect = pygame.Rect(center_x - 45, center_y - 15, 25, 30)
    next_btn_rect = pygame.Rect(center_x + 20, center_y - 15, 25, 30)

    prev_hover = prev_btn_rect.collidepoint(mouse_pos)
    prev_click = prev_hover and pygame.mouse.get_pressed()[0]
    prev_color = COLOR_SPOTIFY_GREEN if prev_click else (COLOR_WHITE if prev_hover else COLOR_TEXT_MUTED)
    pygame.draw.polygon(virtual_surface, prev_color, [(center_x - 35, center_y), (center_x - 25, center_y - 6), (center_x - 25, center_y + 6)])
    
    next_hover = next_btn_rect.collidepoint(mouse_pos)
    next_click = next_hover and pygame.mouse.get_pressed()[0]
    next_color = COLOR_SPOTIFY_GREEN if next_click else (COLOR_WHITE if next_hover else COLOR_TEXT_MUTED)
    pygame.draw.polygon(virtual_surface, next_color, [(center_x + 35, center_y), (center_x + 25, center_y - 6), (center_x + 25, center_y + 6)])
    
    progress_bar_width = 400
    progress_bar_x = center_x - (progress_bar_width // 2)
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

try: pygame.key.stop_text_input()
except: pass

while running:
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
            
        elif event.type == pygame.KEYDOWN:
            if current_page == "Search" and not is_browsing_storage:
                search_input_active = True
                if event.key == pygame.K_BACKSPACE:
                    search_query = search_query[:-1]
                elif event.key == pygame.K_ESCAPE or event.key == pygame.K_RETURN:
                    search_input_active = False
                    try: pygame.key.stop_text_input()
                    except: pass
                else:
                    if len(search_query) < 25 and event.unicode and event.unicode.isprintable():
                        search_query += event.unicode
                        
        elif event.type == pygame.MOUSEBUTTONDOWN:
            mouse_pos = get_virtual_mouse_pos()
            
            if current_page == "Search" or (current_page == "Your Library" and viewing_liked_playlist):
                if is_browsing_storage:
                    if event.button == 4: browser_scroll_offset = max(0, browser_scroll_offset - 1)
                    elif event.button == 5: 
                        if browser_scroll_offset + 11 < len(browser_items):
                            browser_scroll_offset += 1
                else:
                    if event.button == 4: music_grid_scroll_offset = max(0, music_grid_scroll_offset - 30)
                    elif event.button == 5: music_grid_scroll_offset = min(max_music_scroll, music_grid_scroll_offset + 30)

            if event.button == 1:
                is_dragging_grid = True
                last_touch_y = mouse_pos[1]
                total_drag_dy = 0
                
        elif event.type == pygame.MOUSEMOTION:
            if is_dragging_grid:
                mouse_pos = get_virtual_mouse_pos()
                dy = last_touch_y - mouse_pos[1]
                total_drag_dy += abs(dy)
                
                if current_page == "Search" or (current_page == "Your Library" and viewing_liked_playlist):
                    if is_browsing_storage:
                        if dy < -15:
                            browser_scroll_offset = max(0, browser_scroll_offset - 1)
                            last_touch_y = mouse_pos[1]
                        elif dy > 15:
                            if browser_scroll_offset + 11 < len(browser_items):
                                browser_scroll_offset += 1
                            last_touch_y = mouse_pos[1]
                    else:
                        music_grid_scroll_offset += dy
                        music_grid_scroll_offset = max(0, min(max_music_scroll, music_grid_scroll_offset))
                        last_touch_y = mouse_pos[1]

        elif event.type == pygame.MOUSEBUTTONUP:
            mouse_pos = get_virtual_mouse_pos()
            if event.button == 1:
                is_dragging_grid = False
                
                if total_drag_dy < 15:
                    
                    if current_page == "Search" and not is_browsing_storage and search_box_rect.collidepoint(mouse_pos):
                        search_input_active = True
                        try: pygame.key.start_text_input() 
                        except: pass
                    else:
                        search_input_active = False
                        try: pygame.key.stop_text_input()
                        except: pass

                    for rect, target_page in sidebar_rects:
                        if rect.collidepoint(mouse_pos):
                            current_page = target_page
                            is_browsing_storage = False 
                            viewing_liked_playlist = False
                            music_grid_scroll_offset = 0

                    if current_page == "Your Library" and not viewing_liked_playlist:
                        if liked_songs_card_rect.collidepoint(mouse_pos):
                            viewing_liked_playlist = True
                            music_grid_scroll_offset = 0

                    # Master Playlist header action controller updated
                    elif viewing_liked_playlist and current_page == "Your Library" and playlist_play_btn_rect.collidepoint(mouse_pos):
                        if liked_tracks:
                            if current_track["path"] != liked_tracks[0]["path"]:
                                current_track = liked_tracks[0]  # Force selection to the first song layout block
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
                                    
                    else:
                        if current_page == "Search" and add_folder_btn_rect.collidepoint(mouse_pos):
                            is_browsing_storage = True
                            update_browser_contents()
                                
                        # Track Click Handler (Grid or Playlist Table)
                        if current_page in ["Search"] or (current_page == "Your Library" and viewing_liked_playlist):
                            for rect, track in track_rects:
                                content_bottom_margin = 90 if current_track["title"] != "Select a song" else 0
                                if current_page == "Your Library" and viewing_liked_playlist:
                                    clip_rect_bounds = pygame.Rect(230, 315, WIDTH - 230, HEIGHT - 315 - content_bottom_margin)
                                else:
                                    clip_rect_bounds = pygame.Rect(230, 140, WIDTH - 230, HEIGHT - 140 - content_bottom_margin)
                                    
                                if clip_rect_bounds.collidepoint(mouse_pos) and rect.collidepoint(mouse_pos):
                                    current_track = track
                                    playlist_is_playing = False 
                                    is_playing = True 
                                    load_and_play_track(current_track["path"])
                                    
                        # Global Media Controller Hitbox Registrations
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

                            if next_btn_rect.collidepoint(mouse_pos):
                                advance_track(backward=False)
                            elif prev_btn_rect.collidepoint(mouse_pos):
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

                            if star_btn_rect.collidepoint(mouse_pos):
                                if current_track in liked_tracks:
                                    liked_tracks.remove(current_track)
                                else:
                                    liked_tracks.append(current_track)
            
    # Auto-advance sequence track management loop
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

import pygame
import sys
import os

# --- WINDOW & SCALING CONFIGURATION ---
pygame.init()
pygame.font.init()

info = pygame.display.Info()
REAL_WIDTH, REAL_HEIGHT = info.current_w, info.current_h

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

# --- FONTS ---
font_title = pygame.font.SysFont("Arial", 22, bold=True)
font_body = pygame.font.SysFont("Arial", 16, bold=True)
font_small = pygame.font.SysFont("Arial", 14)

# --- APP STATE ---
current_page = "Home"  
current_track = {      
    "title": "Select a song",
    "artist": "No Artist",
    "duration": "0:00"
}
is_playing = False     

# --- MOCK DATA ---
sidebar_items = ["Home", "Search", "Your Library"]

# Predefined tracks have been completely removed to only show your scanned music
track_list = []

# Scanning Engine States
imported_tracks = []
scanned_directories = []  # Tracks paths we've already parsed
search_message = "Tap '+ Add Folder' to search specific phone directories."

# Storage Scan Cycle Index
available_scan_paths = ["/sdcard/Download", "/sdcard/Music", "/sdcard"]
current_path_index = 0

# Global interaction boundaries
track_rects = []
sidebar_rects = []
play_btn_rect = pygame.Rect(0, 0, 0, 0)
add_folder_btn_rect = pygame.Rect(0, 0, 0, 0)

# --- SCANNING ENGINE ---
def scan_next_directory():
    """Scans multiple folders in sequence and appends them together."""
    global imported_tracks, search_message, current_path_index, scanned_directories
    
    target_dir = available_scan_paths[current_path_index]
    
    if os.path.exists(target_dir):
        if target_dir in scanned_directories:
            search_message = f"Folder '{target_dir}' is already scanned!"
        else:
            scanned_directories.append(target_dir)
            track_counter = len(imported_tracks) + 1
            new_songs_found = 0
            
            try:
                for file in os.listdir(target_dir):
                    if file.lower().endswith(('.mp3', '.wav', '.ogg', '.m4a', '.flac')):
                        clean_title = os.path.splitext(file)[0]
                        
                        track_data = {
                            "num": str(track_counter),
                            "title": clean_title,
                            "artist": "Local File",
                            "album": os.path.basename(target_dir) if os.path.basename(target_dir) else "Root Storage",
                            "duration": "Local" 
                        }
                        imported_tracks.append(track_data)
                        track_counter += 1
                        new_songs_found += 1
                
                search_message = f"Added {new_songs_found} tracks from '{target_dir}'. Total local songs: {len(imported_tracks)}"
            except Exception:
                search_message = f"Permission denied trying to scan '{target_dir}'."
    else:
        search_message = f"Folder pathway '{target_dir}' could not be located."

    # Cycle to the next target location for the next tap
    current_path_index = (current_path_index + 1) % len(available_scan_paths)

# --- UI DRAWING FUNCTIONS ---

def get_virtual_mouse_pos():
    real_x, real_y = pygame.mouse.get_pos()
    virtual_x = int(real_x * (WIDTH / REAL_WIDTH))
    virtual_y = int(real_y * (HEIGHT / REAL_HEIGHT))
    return (virtual_x, virtual_y)

def draw_sidebar():
    global sidebar_rects
    sidebar_rects = [] 
    
    sidebar_rect = pygame.Rect(0, 0, 230, HEIGHT - 90)
    pygame.draw.rect(virtual_surface, COLOR_DARK_GREY, sidebar_rect)
    
    logo_text = font_title.render("SpotM-Fi", True, COLOR_SPOTIFY_GREEN)
    virtual_surface.blit(logo_text, (20, 30))
    
    y_offset = 90
    mouse_pos = get_virtual_mouse_pos()
    
    for item in sidebar_items:
        item_rect = pygame.Rect(10, y_offset - 5, 210, 35)
        sidebar_rects.append((item_rect, item))
        
        if item_rect.collidepoint(mouse_pos) or current_page == item:
            pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=5)
            text_color = COLOR_WHITE
        else:
            text_color = COLOR_TEXT_MUTED
            
        text_surf = font_body.render(item, True, text_color)
        virtual_surface.blit(text_surf, (25, y_offset))
        y_offset += 40

def draw_main_content():
    global track_rects, add_folder_btn_rect
    track_rects = [] 
    
    main_rect = pygame.Rect(230, 0, WIDTH - 230, HEIGHT - 90)
    pygame.draw.rect(virtual_surface, COLOR_BLACK, main_rect)
    mouse_pos = get_virtual_mouse_pos()

    if current_page == "Home":
        album_art_rect = pygame.Rect(260, 40, 120, 120)
        pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, album_art_rect, border_radius=8)
        
        type_surf = font_small.render("PUBLIC PLAYLIST", True, COLOR_WHITE)
        virtual_surface.blit(type_surf, (400, 50))
        
        title_surf = font_title.render("Today's Top Hits", True, COLOR_WHITE)
        title_surf = pygame.transform.scale(title_surf, (int(title_surf.get_width()*1.5), int(title_surf.get_height()*1.5)))
        virtual_surface.blit(title_surf, (400, 75))
        
        info_surf = font_small.render("Click any track below to play it!", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(info_surf, (400, 130))
        
        headers = [("#", 260), ("Title", 300), ("Album", 650), ("Duration", 950)]
        for text, x in headers:
            header_surf = font_small.render(text, True, COLOR_TEXT_MUTED)
            virtual_surface.blit(header_surf, (x, 200))
            
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 225), (WIDTH - 40, 225), 1)
        
        y_offset = 240
        if not track_list:
            empty_home_surf = font_body.render("Your playlist is currently empty.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_home_surf, (260, y_offset))
        else:
            for track in track_list:
                track_row_rect = pygame.Rect(250, y_offset - 5, WIDTH - 280, 40)
                track_rects.append((track_row_rect, track))
                
                if track["title"] == current_track["title"]:
                    title_color = COLOR_SPOTIFY_GREEN
                    if track_row_rect.collidepoint(mouse_pos):
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, track_row_rect, border_radius=5)
                elif track_row_rect.collidepoint(mouse_pos):
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, track_row_rect, border_radius=5)
                    title_color = COLOR_WHITE
                else:
                    title_color = COLOR_WHITE
                    
                num_surf = font_body.render(track["num"], True, COLOR_TEXT_MUTED)
                title_surf = font_body.render(track["title"], True, title_color)
                artist_surf = font_small.render(track["artist"], True, COLOR_TEXT_MUTED)
                album_surf = font_small.render(track["album"], True, COLOR_TEXT_MUTED)
                duration_surf = font_small.render(track["duration"], True, COLOR_TEXT_MUTED)
                
                virtual_surface.blit(num_surf, (260, y_offset))
                virtual_surface.blit(title_surf, (300, y_offset))
                virtual_surface.blit(artist_surf, (300, y_offset + 18))
                virtual_surface.blit(album_surf, (650, y_offset + 8))
                virtual_surface.blit(duration_surf, (950, y_offset + 8))
                
                y_offset += 55

    # --- SEARCH PAGE ---
    elif current_page == "Search":
        search_title = font_title.render("Search Results", True, COLOR_WHITE)
        virtual_surface.blit(search_title, (260, 40))
        
        # Interactive UI Add Storage Target Button
        add_folder_btn_rect = pygame.Rect(780, 80, 180, 40)
        if add_folder_btn_rect.collidepoint(mouse_pos):
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, add_folder_btn_rect, border_radius=20)
            btn_color = COLOR_BLACK
        else:
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, add_folder_btn_rect, border_radius=20)
            btn_color = COLOR_WHITE
            
        next_target_lbl = f"+ Add Folder ({available_scan_paths[current_path_index].split('/')[-1]})"
        btn_txt = font_small.render(next_target_lbl, True, btn_color)
        virtual_surface.blit(btn_txt, (795, 92))

        # Dynamic Search Bar Container
        search_box = pygame.Rect(260, 80, 500, 40)
        pygame.draw.rect(virtual_surface, COLOR_WHITE, search_box, border_radius=20)
        search_text = font_small.render(f"  {search_message}", True, COLOR_LIGHT_GREY)
        virtual_surface.blit(search_text, (275, 92))

        headers = [("#", 260), ("Local Title", 300), ("Source Folder", 650), ("Type", 950)]
        for text, x in headers:
            header_surf = font_small.render(text, True, COLOR_TEXT_MUTED)
            virtual_surface.blit(header_surf, (x, 150))
            
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (260, 175), (WIDTH - 40, 175), 1)

        if not imported_tracks:
            empty_surf = font_body.render("No local music loaded. Tap '+ Add Folder' above to search storage locations!", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_surf, (260, 200))
        else:
            y_offset = 190
            for track in imported_tracks:
                track_row_rect = pygame.Rect(250, y_offset - 5, WIDTH - 280, 40)
                track_rects.append((track_row_rect, track)) 
                
                if track["title"] == current_track["title"]:
                    title_color = COLOR_SPOTIFY_GREEN
                    if track_row_rect.collidepoint(mouse_pos):
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, track_row_rect, border_radius=5)
                elif track_row_rect.collidepoint(mouse_pos):
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, track_row_rect, border_radius=5)
                    title_color = COLOR_WHITE
                else:
                    title_color = COLOR_WHITE
                    
                num_surf = font_body.render(track["num"], True, COLOR_TEXT_MUTED)
                title_surf = font_body.render(track["title"], True, title_color)
                artist_surf = font_small.render(track["artist"], True, COLOR_TEXT_MUTED)
                album_surf = font_small.render(track["album"], True, COLOR_TEXT_MUTED)
                duration_surf = font_small.render(track["duration"], True, COLOR_TEXT_MUTED)
                
                virtual_surface.blit(num_surf, (260, y_offset))
                virtual_surface.blit(title_surf, (300, y_offset))
                virtual_surface.blit(artist_surf, (300, y_offset + 18))
                virtual_surface.blit(album_surf, (650, y_offset + 8))
                virtual_surface.blit(duration_surf, (950, y_offset + 8))
                
                y_offset += 55

    elif current_page == "Your Library":
        lib_title = font_title.render("Your Library", True, COLOR_WHITE)
        virtual_surface.blit(lib_title, (260, 40))
        
        card_rect = pygame.Rect(260, 95, 160, 200)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, card_rect, border_radius=8)
        pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, (275, 110, 130, 110), border_radius=4)
        
        card_txt1 = font_body.render("Liked Songs", True, COLOR_WHITE)
        card_txt2 = font_small.render("Playlist • 0 songs", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(card_txt1, (275, 230))
        virtual_surface.blit(card_txt2, (275, 255))

def draw_media_bar():
    global play_btn_rect
    bar_rect = pygame.Rect(0, HEIGHT - 90, WIDTH, 90)
    pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, bar_rect)
    
    now_playing_title = font_body.render(current_track["title"], True, COLOR_WHITE)
    now_playing_artist = font_small.render(current_track["artist"], True, COLOR_TEXT_MUTED)
    virtual_surface.blit(now_playing_title, (20, HEIGHT - 65))
    virtual_surface.blit(now_playing_artist, (20, HEIGHT - 45))
    
    center_x = WIDTH // 2
    center_y = HEIGHT - 60
    
    play_btn_rect = pygame.Rect(center_x - 18, center_y - 18, 36, 36)
    pygame.draw.circle(virtual_surface, COLOR_WHITE, (center_x, center_y), 18)
    
    if not is_playing:
        pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(center_x - 4, center_y - 6), (center_x - 4, center_y + 6), (center_x + 6, center_y)])
    else:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (center_x - 5, center_y - 6, 3, 12))
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (center_x + 2, center_y - 6, 3, 12))
    
    pygame.draw.polygon(virtual_surface, COLOR_TEXT_MUTED, [(center_x - 35, center_y), (center_x - 25, center_y - 6), (center_x - 25, center_y + 6)])
    pygame.draw.polygon(virtual_surface, COLOR_TEXT_MUTED, [(center_x + 35, center_y), (center_x + 25, center_y - 6), (center_x + 25, center_y + 6)])
    
    progress_bar_width = 400
    progress_bar_x = center_x - (progress_bar_width // 2)
    progress_bar_y = HEIGHT - 25
    
    pygame.draw.rect(virtual_surface, COLOR_HOVER, (progress_bar_x, progress_bar_y, progress_bar_width, 4), border_radius=2)
    percent_fill = 0.35 if is_playing else 0.0
    pygame.draw.rect(virtual_surface, COLOR_WHITE, (progress_bar_x, progress_bar_y, int(progress_bar_width * percent_fill), 4), border_radius=2)
    
    time_start = font_small.render("1:12" if is_playing else "0:00", True, COLOR_TEXT_MUTED)
    time_end = font_small.render(current_track["duration"], True, COLOR_TEXT_MUTED)
    virtual_surface.blit(time_start, (progress_bar_x - 35, progress_bar_y - 6))
    virtual_surface.blit(time_end, (progress_bar_x + progress_bar_width + 10, progress_bar_y - 6))

# --- MAIN LOOP ---
running = True
while running:
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
            
        elif event.type == pygame.MOUSEBUTTONDOWN:
            if event.button == 1: 
                mouse_pos = get_virtual_mouse_pos()
                
                # Navigation clicks
                for rect, target_page in sidebar_rects:
                    if rect.collidepoint(mouse_pos):
                        current_page = target_page
                        
                # Search page [+ Add Folder] click handler
                if current_page == "Search" and add_folder_btn_rect.collidepoint(mouse_pos):
                    scan_next_directory()
                        
                # Row selection logic
                if current_page in ["Home", "Search"]:
                    for rect, track in track_rects:
                        if rect.collidepoint(mouse_pos):
                            current_track = track
                            is_playing = True 
                            
                # Bottom play bar click
                if play_btn_rect.collidepoint(mouse_pos):
                    if current_track["title"] != "Select a song": 
                        is_playing = not is_playing
            
    virtual_surface.fill(COLOR_BLACK)
    
    draw_main_content()
    draw_sidebar()
    draw_media_bar()
    
    scaled_frame = pygame.transform.scale(virtual_surface, (REAL_WIDTH, REAL_HEIGHT))
    screen.blit(scaled_frame, (0, 0))
    
    pygame.display.flip()
    clock.tick(60)

pygame.quit()
sys.exit()

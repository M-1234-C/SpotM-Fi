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
COLOR_CARD_BG = (30, 30, 30)

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

# --- DATA STORAGE ---
sidebar_items = ["Home", "Search", "Your Library"]
track_list = []
imported_tracks = []
saved_directories = []  

# Browser & Search State Engine
is_browsing_storage = False
search_input_active = False
search_query = ""

ROOT_PATH = "/storage/emulated/0" if os.path.exists("/storage/emulated/0") else "/sdcard"
current_browser_path = ROOT_PATH
browser_items = []  
browser_scroll_offset = 0
music_grid_scroll_offset = 0  

search_message = "Tap '+ Add Folder' to open the built-in storage browser."

# Global interaction boundaries
track_rects = []
sidebar_rects = []
browser_rects = []
search_box_rect = pygame.Rect(260, 80, 500, 40)
play_btn_rect = pygame.Rect(0, 0, 0, 0)
add_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
select_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
cancel_browser_btn_rect = pygame.Rect(0, 0, 0, 0)

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
                        "duration": "Media" 
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
        
        if item_rect.collidepoint(mouse_pos) or (current_page == item and not is_browsing_storage):
            pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=5)
            text_color = COLOR_WHITE
        else:
            text_color = COLOR_TEXT_MUTED
            
        text_surf = font_body.render(item, True, text_color)
        virtual_surface.blit(text_surf, (25, y_offset))
        y_offset += 40

def draw_main_content():
    global track_rects, add_folder_btn_rect, browser_rects, select_folder_btn_rect, cancel_browser_btn_rect
    track_rects = []
    browser_rects = []
    
    main_rect = pygame.Rect(230, 0, WIDTH - 230, HEIGHT - 90)
    pygame.draw.rect(virtual_surface, COLOR_BLACK, main_rect)
    mouse_pos = get_virtual_mouse_pos()

    # --- STORAGE BROWSER VIEW ---
    if is_browsing_storage and current_page == "Search":
        browser_title = font_title.render("Device Storage Explorer", True, COLOR_WHITE)
        virtual_surface.blit(browser_title, (260, 40))
        
        path_lbl = font_small.render(f"Path: {current_browser_path}", True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(path_lbl, (260, 75))
        
        select_folder_btn_rect = pygame.Rect(730, 35, 160, 35)
        cancel_browser_btn_rect = pygame.Rect(900, 35, 100, 35)
        
        sf_color = COLOR_SPOTIFY_GREEN if select_folder_btn_rect.collidepoint(mouse_pos) else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, sf_color, select_folder_btn_rect, border_radius=15)
        sf_lbl = font_small.render("✓ Select Current", True, COLOR_WHITE if sf_color == COLOR_LIGHT_GREY else COLOR_BLACK)
        virtual_surface.blit(sf_lbl, (755, 44))
        
        cc_color = COLOR_HOVER if cancel_browser_btn_rect.collidepoint(mouse_pos) else COLOR_LIGHT_GREY
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
            
            if item_row_rect.collidepoint(mouse_pos):
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

    # --- HOME PAGE ---
    elif current_page == "Home":
        pass  

    # --- SEARCH PAGE ---
    elif current_page == "Search":
        search_title = font_title.render("Search Results", True, COLOR_WHITE)
        virtual_surface.blit(search_title, (260, 40))
        
        add_folder_btn_rect = pygame.Rect(780, 80, 180, 40)
        if add_folder_btn_rect.collidepoint(mouse_pos):
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
        for track in imported_tracks:
            if search_query.lower() in track["raw_title"].lower() or search_query.lower() in track["album"].lower():
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
            
            # Setup a true clipping region so boxes smoothly slice in/out of view under the search bar
            clip_rect = pygame.Rect(230, 140, WIDTH - 230, HEIGHT - 140 - 90)
            virtual_surface.set_clip(clip_rect)
            
            for index, track in enumerate(filtered_tracks):
                col = index % cols
                row = index // cols
                
                box_x = start_x + (col * (card_width + gap_x))
                box_y = start_y + (row * (card_height + gap_y)) - music_grid_scroll_offset
                
                card_rect = pygame.Rect(box_x, box_y, card_width, card_height + 40)
                
                # Only process boxes that are actively inside the scrollable clipping view
                if card_rect.colliderect(clip_rect):
                    track_rects.append((card_rect, track))
                    
                    if card_rect.collidepoint(mouse_pos):
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

            # Remove clip boundary so the rest of the UI continues drawing normally above the tracks
            virtual_surface.set_clip(None)

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
            
        elif event.type == pygame.KEYDOWN:
            if current_page == "Search" and not is_browsing_storage:
                search_input_active = True  # Automatically focus Search bar if typing on this page
                if event.key == pygame.K_BACKSPACE:
                    search_query = search_query[:-1]
                elif event.key == pygame.K_ESCAPE:
                    search_query = ""
                    search_input_active = False
                else:
                    # Ignore arbitrary control system keystrokes using .isprintable() check
                    if len(search_query) < 25 and event.unicode.isprintable():
                        search_query += event.unicode
                        
        elif event.type == pygame.MOUSEBUTTONDOWN:
            mouse_pos = get_virtual_mouse_pos()
            
            if current_page == "Search":
                if is_browsing_storage:
                    if event.button == 4: 
                        if browser_scroll_offset > 0:
                            browser_scroll_offset -= 1
                    elif event.button == 5: 
                        if browser_scroll_offset + 11 < len(browser_items):
                            browser_scroll_offset += 1
                else:
                    if event.button == 4: 
                        music_grid_scroll_offset = max(0, music_grid_scroll_offset - 30)
                    elif event.button == 5: 
                        music_grid_scroll_offset += 30

            if event.button == 1: 
                # Click verification logic updated
                if current_page == "Search" and not is_browsing_storage and search_box_rect.collidepoint(mouse_pos):
                    search_input_active = True
                else:
                    search_input_active = False

                for rect, target_page in sidebar_rects:
                    if rect.collidepoint(mouse_pos):
                        current_page = target_page
                        is_browsing_storage = False 

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
                            
                    if current_page in ["Home", "Search"]:
                        for rect, track in track_rects:
                            # Verify mouse clicks are inside the valid clipping scroll area frame
                            clip_rect_bounds = pygame.Rect(230, 140, WIDTH - 230, HEIGHT - 140 - 90)
                            if clip_rect_bounds.collidepoint(mouse_pos) and rect.collidepoint(mouse_pos):
                                current_track = track
                                is_playing = True 
                                
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

import json
import math
import matplotlib.pyplot as plt
import os

def draw_turtle_path(turns, title, filename, label_vertices=False, clockwise_labels=False):
    # Turtle graphics simulator
    x, y = 0.0, 0.0
    # Start heading at 0 degrees
    heading = 0.0
    
    xs = [x]
    ys = [y]
    
    # We are using Cartesian coordinates where 0 degrees is positive x axis.
    # Positive turn is counter-clockwise.
    for turn in turns:
        # First turn the turtle
        heading = (heading + turn) % 360
        rad = math.radians(heading)
        
        # Walk distance 1
        x += math.cos(rad)
        y += math.sin(rad)
        
        xs.append(x)
        ys.append(y)
        
    plt.figure(figsize=(8, 8))
    plt.plot(xs, ys, 'b-', linewidth=2)
    plt.fill(xs, ys, 'lightblue', alpha=0.5)
    
    if label_vertices:
        # Label each vertex (except the last one which is same as first)
        M = len(xs) - 1
        for i in range(M):
            plt.plot(xs[i], ys[i], 'ro', markersize=5)
            # Offset the label slightly so it's readable
            label_idx = (-i) % M if clockwise_labels else i
            
            if clockwise_labels:
                cw_turn = -turns[i]
                norm_turn = (cw_turn + 180) % 360 - 180
                text_label = f"v{label_idx}\n{int(norm_turn)}°"
            else:
                norm_turn = (turns[i] + 180) % 360 - 180
                text_label = f"v{label_idx}\n{int(norm_turn)}°"
                
            plt.text(xs[i], ys[i] + 0.1, text_label, fontsize=10, ha='center', va='bottom', fontweight='bold', color='darkred')
    else:
        plt.plot(xs, ys, 'r.', markersize=4)

    plt.title(title, fontsize=16)
    plt.axis('equal')
    plt.grid(True, linestyle='--', alpha=0.6)
    
    plt.savefig(filename, bbox_inches='tight', dpi=150)
    plt.close()
    print(f"Saved {filename}")

def draw_ccw_annotated_tile(turns, title, filename):
    # Turtle graphics simulator
    x, y = 0.0, 0.0
    heading = 0.0
    
    xs, ys = [x], [y]
    
    for turn in turns:
        heading = (heading + turn) % 360
        rad = math.radians(heading)
        x += math.cos(rad)
        y += math.sin(rad)
        xs.append(x)
        ys.append(y)
        
    plt.figure(figsize=(10, 10))
    plt.plot(xs, ys, 'k-', linewidth=3)
    plt.fill(xs, ys, 'aliceblue', alpha=0.4)
    
    M = len(xs) - 1
    cx, cy = sum(xs[:-1])/M, sum(ys[:-1])/M
    
    for i in range(M):
        vx, vy = xs[i], ys[i]
        plt.plot(vx, vy, 'ro', markersize=8)
        
        # Direction from centroid to vertex (outward)
        dx, dy = vx - cx, vy - cy
        dist = math.sqrt(dx**2 + dy**2)
        
        # Vertex label (outside)
        plt.text(vx + dx/dist*0.18, vy + dy/dist*0.18, f"v{i}", 
                 fontsize=14, ha='center', va='center', fontweight='bold', color='darkblue')
        
        # Exterior turn angle (further outside)
        ext_t = (turns[i] + 180) % 360 - 180
        plt.text(vx + dx/dist*0.38, vy + dy/dist*0.38, f"{int(ext_t)}°", 
                 fontsize=11, ha='center', va='center', color='darkred', fontweight='bold')
        
        # Interior angle (inside)
        # Interior angle = 180 - exterior turn
        int_a = 180 - ext_t
        plt.text(vx - dx/dist*0.18, vy - dy/dist*0.18, f"{int(int_a)}°", 
                 fontsize=12, ha='center', va='center', color='purple', fontweight='bold')
        
        # Edge label (originating vertex)
        mx, my = (xs[i] + xs[i+1])/2, (ys[i] + ys[i+1])/2
        ex, ey = mx - cx, my - cy
        edist = math.sqrt(ex**2 + ey**2)
        plt.text(mx + ex/edist*0.12, my + ey/edist*0.12, str(i), 
                 fontsize=15, ha='center', va='center', fontweight='black', color='forestgreen',
                 bbox=dict(boxstyle='circle,pad=0.1', facecolor='white', alpha=0.9, edgecolor='forestgreen'))

    plt.title(title, fontsize=20, pad=20)
    plt.axis('equal')
    plt.axis('off')
    plt.savefig(filename, bbox_inches='tight', dpi=200)
    plt.close()
    print(f"Saved {filename}")

def main():
    # Use the CCW normalized file if available
    json_file = "mystic_4_boundaries_turning_ccw.json"
    if not os.path.exists(json_file):
        json_file = "mystic_4_boundaries_turning.json"
        
    with open(json_file, "r") as f:
        data = json.load(f)
        
    # 1. Draw the CCW annotated single tile
    single_tile = next((p for p in data if p["patch_size"] == 1), None)
    if single_tile:
        turns = [e["turn_angle"] for e in single_tile["boundary"]]
        draw_ccw_annotated_tile(turns, "Single Spectre Tile: CCW Traversal & Vertex-Edge Labels", 
                               "single_tile_annotated_ccw.png")
                         
    # 2. Draw Patch 1 (size 17)
    patch1 = data[0]
    turns1 = [e["turn_angle"] for e in patch1["boundary"]]
    draw_turtle_path(turns1, f"Patch {patch1['patch_id']} Boundary (Size: {patch1['patch_size']} tiles)", 
                     "patch_1.png")
                     
    # 3. Draw Patch 2 (size 85)
    patch2 = next((p for p in data if p["patch_id"] == 913), data[1])
    turns2 = [e["turn_angle"] for e in patch2["boundary"]]
    draw_turtle_path(turns2, f"Patch {patch2['patch_id']} Boundary (Size: {patch2['patch_size']} tiles)", 
                     f"patch_{patch2['patch_id']}.png")

if __name__ == "__main__":
    main()

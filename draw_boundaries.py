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

def main():
    artifact_dir = "/home/tryggth2009/.gemini/antigravity/brain/6c7daf1a-4d9d-43f2-b8e4-15543a37dfe5/artifacts"
    os.makedirs(artifact_dir, exist_ok=True)
    
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    # 1. Draw a single tile and label vertices
    # Find a size 1 patch
    single_tile = next((p for p in data if p["patch_size"] == 1), None)
    if single_tile:
        turns = [e["turn_angle"] for e in single_tile["boundary"]]
        draw_turtle_path(turns, "Single Spectre Tile (Turtle Path)", 
                         os.path.join(artifact_dir, "single_tile_cw_turns.png"), 
                         label_vertices=True, clockwise_labels=True)
                         
    # 2. Draw Patch 1 (size 17)
    patch1 = data[0]
    turns1 = [e["turn_angle"] for e in patch1["boundary"]]
    draw_turtle_path(turns1, f"Patch {patch1['patch_id']} Boundary (Size: {patch1['patch_size']} tiles)", 
                     os.path.join(artifact_dir, "patch_1.png"))
                     
    # 3. Draw Patch 2 (size 85)
    patch2 = data[1]
    turns2 = [e["turn_angle"] for e in patch2["boundary"]]
    draw_turtle_path(turns2, f"Patch {patch2['patch_id']} Boundary (Size: {patch2['patch_size']} tiles)", 
                     os.path.join(artifact_dir, "patch_2.png"))

if __name__ == "__main__":
    main()

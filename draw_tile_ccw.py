import json
import math
import numpy as np
import matplotlib.pyplot as plt
import os

def draw_annotated_tile(turns, title, filename):
    # Turtle graphics simulator
    x, y = 0.0, 0.0
    # Start heading at 0 degrees (pointing right)
    heading = 0.0
    
    xs = [x]
    ys = [y]
    
    # We are using Cartesian coordinates where 0 degrees is positive x axis.
    # Positive turn is counter-clockwise.
    # The turns are exterior angles.
    for turn in turns:
        # Turn first
        heading = (heading + turn) % 360
        rad = math.radians(heading)
        
        # Walk distance 1
        x += math.cos(rad)
        y += math.sin(rad)
        
        xs.append(x)
        ys.append(y)
        
    plt.figure(figsize=(10, 10))
    # Plot edges
    plt.plot(xs, ys, 'k-', linewidth=3, alpha=0.8)
    plt.fill(xs, ys, 'azure', alpha=0.3)
    
    M = len(xs) - 1 # 14
    
    # Calculate center for labels
    cx = sum(xs[:-1]) / M
    cy = sum(ys[:-1]) / M
    
    for i in range(M):
        # Vertex i
        vx, vy = xs[i], ys[i]
        plt.plot(vx, vy, 'ro', markersize=8)
        
        # Label Vertex v_i
        # Vector from center to vertex for offsetting
        dx, dy = vx - cx, vy - cy
        dist = math.sqrt(dx**2 + dy**2)
        offset = 0.15
        lx, ly = vx + (dx/dist)*offset, vy + (dy/dist)*offset
        
        plt.text(lx, ly, f"v{i}", fontsize=14, ha='center', va='center', 
                 fontweight='bold', color='darkblue', 
                 bbox=dict(facecolor='white', alpha=0.8, edgecolor='none', boxstyle='round,pad=0.1'))
        
        # Label Turn Angle at v_i
        # The turn in the turtle walk that occurs at v_i is turns[i]
        # (Since we turn then move, the first turn happens at v0)
        t_val = turns[i]
        # Normalize to [-180, 180]
        norm_t = (t_val + 180) % 360 - 180
        
        # Place turn label slightly inside? 
        # Or just below the vertex label.
        tx, ty = vx + (dx/dist)*0.35, vy + (dy/dist)*0.35
        # Actually, let's put it closer to the vertex
        plt.text(vx + (dx/dist)*0.1, vy + (dy/dist)*0.1, f"{int(norm_t)}°", 
                 fontsize=11, ha='center', va='center', color='darkred', fontweight='bold')

    # Label Edges
    for i in range(M):
        # Edge from v_i to v_{i+1}
        x1, y1 = xs[i], ys[i]
        x2, y2 = xs[i+1], ys[i+1]
        
        mx, my = (x1 + x2) / 2, (y1 + y2) / 2
        
        # Offset edge label outwards
        ex, ey = mx - cx, my - cy
        edist = math.sqrt(ex**2 + ey**2)
        elx, ely = mx + (ex/edist)*0.12, my + (ey/edist)*0.12
        
        plt.text(elx, ely, str(i), fontsize=15, ha='center', va='center',
                 fontweight='black', color='forestgreen',
                 bbox=dict(boxstyle='circle,pad=0.1', facecolor='white', alpha=0.9, edgecolor='forestgreen', linewidth=2))

    plt.title(title, fontsize=20, pad=30, fontweight='bold')
    plt.axis('equal')
    plt.axis('off')
    
    plt.savefig(filename, bbox_inches='tight', dpi=200)
    print(f"Saved {filename}")

def main():
    # Use the CCW unique file we created
    filename = "mystic_4_boundaries_turning_ccw.json"
    if not os.path.exists(filename):
        # Fallback to the other one if needed
        filename = "mystic_4_boundaries_turning_ccw_unique.json"
        
    with open(filename, "r") as f:
        data = json.load(f)
    
    # Pick the first single tile (it should be 360 sum)
    single_tile = next((p for p in data if p["patch_size"] == 1), None)
    if not single_tile:
        print("No single tile found!")
        return
        
    turns = [e["turn_angle"] for e in single_tile["boundary"]]
    
    # Double check sum
    s = sum(turns)
    print(f"Sum of turns: {s}")
    
    draw_annotated_tile(turns, "Spectre Tile: Counter-Clockwise Traversal", "single_tile_annotated_ccw.png")

if __name__ == "__main__":
    main()

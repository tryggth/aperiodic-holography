import json
import math
import numpy as np

# Convert an angle in degrees to a bucket index 0..11
def angle_to_idx(ang):
    return int(round(ang / 30.0)) % 12

def reconstruct_absolute_angles(turns):
    # turns: list of turn angles
    # Start at 0, accumulate turns
    abs_angles = []
    curr = 0
    for t in turns:
        curr = (curr + t) % 360
        abs_angles.append(curr)
    return abs_angles

def get_parikh_vector(abs_angles):
    # returns a 12-dimensional vector counting edge frequencies
    vec = [0]*12
    for a in abs_angles:
        vec[angle_to_idx(a)] += 1
    return vec

def get_reduced_vector(parikh):
    # returns a 6-dimensional vector: net edges in directions 0..5
    # e_6 is -e_0, so net count is count(0) - count(6)
    vec = [0]*6
    for i in range(6):
        vec[i] = parikh[i] - parikh[i+6]
    return vec

def main():
    # 1. Analyze the single Spectre tile
    # We can get its turns from the JSON by looking at a patch of size 1
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    single_tiles = [p for p in data if p["patch_size"] == 1]
    if single_tiles:
        t1 = single_tiles[0]
        turns = [e["turn_angle"] for e in t1["boundary"]]
        abs_angles = reconstruct_absolute_angles(turns)
        pv = get_parikh_vector(abs_angles)
        rv = get_reduced_vector(pv)
        print("Single Spectre Tile Analysis:")
        print("Parikh Vector (12D):", pv)
        print("Reduced Vector (6D):", rv)
        
    # Let's check patches of size 2
    size_2 = [p for p in data if p["patch_size"] == 2]
    if size_2:
        print("\nSize 2 Patch Analysis:")
        for i in range(min(3, len(size_2))):
            t = size_2[i]
            turns = [e["turn_angle"] for e in t["boundary"]]
            abs_angles = reconstruct_absolute_angles(turns)
            rv2 = get_reduced_vector(get_parikh_vector(abs_angles))
            print(f"Patch {t['patch_id']} (size 2) Reduced Vector:", rv2)
            
            # Difference from single tile
            diff = [rv2[k] - rv[k] for k in range(6)]
            print(f"  Difference from size 1:", diff)

if __name__ == "__main__":
    main()

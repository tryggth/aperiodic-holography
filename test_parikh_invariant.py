import json
import math
from collections import Counter

def angle_to_idx(ang):
    return int(round(ang / 30.0)) % 12

def reconstruct_absolute_angles(turns):
    abs_angles = []
    curr = 0
    for t in turns:
        curr = (curr + t) % 360
        abs_angles.append(curr)
    return abs_angles

def get_6d_parikh(abs_angles):
    vec = [0]*6
    for a in abs_angles:
        vec[angle_to_idx(a) % 6] += 1
    # Since each edge has a pair, divide by 2?
    # Wait, if the boundary traverses an edge in direction d, it does not traverse d+6.
    # The external boundary is a directed cycle.
    # So if we just take angle % 6, we count both d and d+6 together.
    return vec

def main():
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    for p in data[:5]:
        turns = [e["turn_angle"] for e in p["boundary"]]
        abs_angles = reconstruct_absolute_angles(turns)
        vec6 = get_6d_parikh(abs_angles)
        print(f"Patch {p['patch_id']} (size {p['patch_size']}):")
        print("  6D Vector:", vec6)
        print("  Mod 2:    ", [x % 2 for x in vec6])
        
if __name__ == "__main__":
    main()

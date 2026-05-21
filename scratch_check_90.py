import json
from collections import Counter

def main():
    file_path = "mystic_4_boundaries_turning_ccw.json"
    print(f"Reading {file_path}...")
    with open(file_path, 'r') as f:
        patches = json.load(f)
    
    print(f"Loaded {len(patches)} patches.")
    
    no_left_90_patches = []
    unique_angles = set()
    left_90_counts = []
    
    for patch in patches:
        patch_id = patch.get("patch_id")
        patch_size = patch.get("patch_size")
        boundary = patch.get("boundary", [])
        
        counts = Counter()
        for step in boundary:
            angle = step.get("turn_angle")
            if angle is not None:
                unique_angles.add(angle)
                counts[angle] += 1
        
        num_left_90 = counts[90]
        left_90_counts.append(num_left_90)
        
        if num_left_90 == 0:
            no_left_90_patches.append((patch_id, patch_size))
            
    print(f"Found {len(no_left_90_patches)} patches with no left 90-degree turn.")
    print(f"All unique turn angles present in the boundary paths: {sorted(list(unique_angles))}")
    print(f"Min left 90-degree turns in a boundary path: {min(left_90_counts)}")
    print(f"Max left 90-degree turns in a boundary path: {max(left_90_counts)}")
    print(f"Average left 90-degree turns in a boundary path: {sum(left_90_counts) / len(left_90_counts):.2f}")

if __name__ == "__main__":
    main()

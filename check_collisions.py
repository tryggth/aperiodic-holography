import json

def get_canonical_word(turns):
    # returns the lexicographically smallest cyclic permutation
    n = len(turns)
    best = turns
    for i in range(1, n):
        shifted = turns[i:] + turns[:i]
        if shifted < best:
            best = shifted
    return tuple(best)

def main():
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    canonical_to_patches = {}
    
    for patch in data:
        pid = patch["patch_id"]
        turns = [edge["turn_angle"] for edge in patch["boundary"]]
        canon = get_canonical_word(turns)
        
        if canon not in canonical_to_patches:
            canonical_to_patches[canon] = []
        canonical_to_patches[canon].append(pid)
        
    collisions = {k: v for k, v in canonical_to_patches.items() if len(v) > 1}
    print(f"Total unique boundaries (up to cyclic shift): {len(canonical_to_patches)}")
    print(f"Number of collisions (different patches with same boundary shape): {len(collisions)}")
    
    if collisions:
        for canon, pids in list(collisions.items())[:5]:
            print(f"Boundary of length {len(canon)} shared by patches: {pids}")

if __name__ == "__main__":
    main()

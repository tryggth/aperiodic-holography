import json

def get_canonical_word(turns):
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
        size = patch["patch_size"]
        turns = [edge["turn_angle"] for edge in patch["boundary"]]
        canon = get_canonical_word(turns)
        
        if canon not in canonical_to_patches:
            canonical_to_patches[canon] = []
        canonical_to_patches[canon].append((pid, size))
        
    collisions = {k: v for k, v in canonical_to_patches.items() if len(v) > 1}
    
    counterexamples = []
    
    for canon, p_list in collisions.items():
        # Check if they all have the same patch_size
        sizes = [size for pid, size in p_list]
        if len(set(sizes)) > 1:
            counterexamples.append((canon, p_list))
            
    print(f"Total boundary shapes appearing multiple times: {len(collisions)}")
    
    if counterexamples:
        print("\n!!! COUNTEREXAMPLES FOUND !!!")
        print("These boundary shapes have DIFFERENT internal patch sizes (different tilings):")
        for canon, p_list in counterexamples:
            print(f"Boundary length {len(canon)}, sizes: {p_list}")
    else:
        print("\nAll patches with identical boundary shapes have the exact same number of internal tiles.")
        print("This strongly supports the theorem: the boundary shape uniquely forces the internal tiling.")

if __name__ == "__main__":
    main()

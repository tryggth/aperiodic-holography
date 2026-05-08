import json

def angle_to_letter(ang):
    # Map absolute angle to an index 0..11
    idx = int(round(ang / 30.0)) % 12
    # Uppercase A-F for 0..5, Lowercase a-f for 6..11 (inverses)
    if idx < 6:
        return chr(ord('A') + idx)
    else:
        return chr(ord('a') + (idx - 6))

def reconstruct_absolute_angles(turns):
    # To get canonical orientation, we will just assume the first edge points at 0 degrees.
    # The absolute orientation doesn't change the word structure, just applies a global cyclic shift to the alphabet.
    abs_angles = []
    curr = 0
    for t in turns:
        # The turn is applied *after* traversing the edge in my previous logic,
        # but wait, the json says:
        # "angle": turn_angle, "distance": 1
        # The turn_angle is the turn from the INCOMING edge to the OUTGOING edge.
        # If the first incoming edge was at angle 0, then the first outgoing edge is at 0 + turn_angle.
        curr = (curr + t) % 360
        abs_angles.append(curr)
    return abs_angles

def main():
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    for patch in data:
        turns = [e["turn_angle"] for e in patch["boundary"]]
        abs_angles = reconstruct_absolute_angles(turns)
        
        word_chars = [angle_to_letter(a) for a in abs_angles]
        word = "".join(word_chars)
        
        # Add the boundary word to the patch dictionary
        patch["boundary_word"] = word
        
    with open("mystic_4_boundary_words.json", "w") as f:
        json.dump(data, f, indent=2)
        
    print(f"Generated {len(data)} non-abelian boundary words.")
    print("Example (Patch 1):", data[0]["boundary_word"])

if __name__ == "__main__":
    main()

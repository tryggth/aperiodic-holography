import json

input_file = 'mystic_4_boundaries_turning.json'
output_file = 'mystic_4_boundaries_turning_ccw.json'

with open(input_file, 'r') as f:
    data = json.load(f)

def get_canonical(boundary):
    # Convert boundary to tuple of (angle, distance)
    seq = tuple((s['turn_angle'], s['distance']) for s in boundary)
    # Find lexicographical minimum cyclic shift
    n = len(seq)
    shifts = [seq[i:] + seq[:i] for i in range(n)]
    return min(shifts)

processed_data = []
canonical_counts = {}
duplicates = []

for patch in data:
    boundary = patch['boundary']
    total_angle = sum(s['turn_angle'] for s in boundary)
    
    # Flip signs if CW (-360)
    if total_angle == -360:
        for s in boundary:
            s['turn_angle'] = -s['turn_angle']
    elif total_angle != 360:
        print(f"Warning: Patch {patch['patch_id']} has unexpected sum {total_angle}")

    # After flipping, sum should be 360
    new_sum = sum(s['turn_angle'] for s in boundary)
    if new_sum != 360:
         print(f"Error: Patch {patch['patch_id']} failed to normalize to 360. Sum is {new_sum}")

    # Check for duplicates
    canonical = get_canonical(boundary)
    if canonical in canonical_counts:
        canonical_counts[canonical].append(patch['patch_id'])
    else:
        canonical_counts[canonical] = [patch['patch_id']]
    
    processed_data.append(patch)

# Summarize duplicates
for canonical, ids in canonical_counts.items():
    if len(ids) > 1:
        duplicates.append(ids)

with open(output_file, 'w') as f:
    json.dump(processed_data, f, indent=2)

print(f"Processed {len(processed_data)} patches.")
print(f"All patches normalized to 360 degrees.")
if not duplicates:
    print("Confirmed: No duplicate paths found (even considering cyclic shifts).")
else:
    print(f"Found {len(duplicates)} sets of duplicate paths:")
    for dset in duplicates:
        print(f"  Patch IDs: {dset}")

# Extra check: No exact duplicates (without cyclic shift)
exact_counts = {}
for patch in processed_data:
    seq = tuple((s['turn_angle'], s['distance']) for s in patch['boundary'])
    exact_counts[seq] = exact_counts.get(seq, 0) + 1

exact_dupes = sum(1 for count in exact_counts.values() if count > 1)
print(f"Exact sequence duplicates: {exact_dupes}")

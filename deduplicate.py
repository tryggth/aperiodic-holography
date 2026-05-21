import json

input_file = 'mystic_4_boundaries_turning_ccw.json'
output_file = 'mystic_4_boundaries_turning_ccw.json' # Overwriting with unique version

with open(input_file, 'r') as f:
    data = json.load(f)

def get_canonical(boundary):
    seq = tuple((s['turn_angle'], s['distance']) for s in boundary)
    n = len(seq)
    return min(seq[i:] + seq[:i] for i in range(n))

unique_data = []
seen_canonical = set()

for patch in data:
    canonical = get_canonical(patch['boundary'])
    if canonical not in seen_canonical:
        seen_canonical.add(canonical)
        unique_data.append(patch)

with open(output_file, 'w') as f:
    json.dump(unique_data, f, indent=2)

print(f"Removed {len(data) - len(unique_data)} duplicates.")
print(f"File now contains {len(unique_data)} unique paths.")

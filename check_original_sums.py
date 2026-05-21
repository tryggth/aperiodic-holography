import json

file_path = 'mystic_4_boundaries_turning.json'

with open(file_path, 'r') as f:
    data = json.load(f)

sums = {}
for patch in data:
    boundary = patch.get('boundary', [])
    total_angle = sum(segment.get('turn_angle', 0) for segment in boundary)
    sums[total_angle] = sums.get(total_angle, 0) + 1

print(f"Original file '{file_path}' sums distribution:")
for angle, count in sums.items():
    print(f"  {angle} degrees: {count} patches")

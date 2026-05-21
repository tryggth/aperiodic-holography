import json

file_path = 'mystic_4_boundaries_turning_ccw.json'

with open(file_path, 'r') as f:
    data = json.load(f)

errors = []
for patch in data:
    patch_id = patch.get('patch_id')
    boundary = patch.get('boundary', [])
    total_angle = sum(segment.get('turn_angle', 0) for segment in boundary)
    
    if total_angle != 360:
        errors.append((patch_id, total_angle))

if not errors:
    print(f"All {len(data)} patches sum to exactly 360 degrees.")
else:
    print(f"Found {len(errors)} patches with incorrect total angles:")
    for pid, angle in errors[:10]:
        print(f"  Patch {pid}: {angle} degrees")
    if len(errors) > 10:
        print(f"  ... and {len(errors) - 10} more.")

import json

input_file = 'mystic_4_boundaries_turning.json'
output_file = 'mystic_4_boundaries_turning_ccw.json'

with open(input_file, 'r') as f:
    data = json.load(f)

for patch in data:
    if 'boundary' in patch:
        for segment in patch['boundary']:
            if 'turn_angle' in segment:
                segment['turn_angle'] = -segment['turn_angle']

with open(output_file, 'w') as f:
    json.dump(data, f, indent=2)

print(f"Successfully created {output_file} with reversed turn angles.")

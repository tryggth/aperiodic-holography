import json

with open('mystic_4_boundaries_turning.json', 'r') as f:
    data = json.load(f)

# Find the single tile
p = next(p for p in data if p['patch_size'] == 1)
turns = [e['turn_angle'] for e in p['boundary']]
M = len(turns)

print("| Vertex Label | CW Turn at Vertex | Original CCW Turn |")
print("| :--- | :--- | :--- |")
for k in range(M):
    point_idx = (-k) % M
    ccw_turn = turns[point_idx]
    
    # normalize to -180 to 180
    ccw_norm = (ccw_turn + 180) % 360 - 180
    cw_norm = -ccw_norm
    
    print(f"| v{k} | {cw_norm}° | {ccw_norm}° |")

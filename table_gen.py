turns = [60, 0, 90, 30, 120, 60, 330, 270, 0, 330, 240, 270, 180, 210]
M = 14

def normalize(angle):
    a = angle % 360
    if a > 180:
        a -= 360
    return a

print("| Vertex Label | Corresponding CCW Point | CCW Turn at Vertex | CW Turn at Vertex |")
print("| :--- | :--- | :--- | :--- |")
for k in range(M):
    point_idx = (-k) % M
    ccw_turn = turns[point_idx]
    cw_turn = -ccw_turn
    
    ccw_norm = normalize(ccw_turn)
    cw_norm = normalize(cw_turn)
    print(f"| v{k} | Point {point_idx} | {ccw_norm}° | {cw_norm}° |")

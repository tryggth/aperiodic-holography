import numpy as np

class pt:
    def __init__(self, x, y):
        self.x = x
        self.y = y

SPECTRE_POINTS = [
    pt(0,                0),
    pt(1.0,              0.0),
    pt(1.5,              -np.sqrt(3)/2),
    pt(1.5+np.sqrt(3)/2, 0.5-np.sqrt(3)/2),
    pt(1.5+np.sqrt(3)/2, 1.5-np.sqrt(3)/2),
    pt(2.5+np.sqrt(3)/2, 1.5-np.sqrt(3)/2),
    pt(3+np.sqrt(3)/2,   1.5),
    pt(3.0,              2.0),
    pt(3-np.sqrt(3)/2,   1.5),
    pt(2.5-np.sqrt(3)/2, 1.5+np.sqrt(3)/2),
    pt(1.5-np.sqrt(3)/2, 1.5+np.sqrt(3)/2),
    pt(0.5-np.sqrt(3)/2, 1.5+np.sqrt(3)/2),
    pt(-np.sqrt(3)/2,    1.5),
    pt(0.0,              1.0)
]

def get_angle(p1, p2, p3):
    # Angle at p2
    v1 = np.array([p1.x - p2.x, p1.y - p2.y])
    v2 = np.array([p3.x - p2.x, p3.y - p2.y])
    
    # Use cross product to get signed angle (to distinguish reflex angles)
    # But for interior angles of a CCW polygon, it's simpler.
    # Let's use atan2.
    ang1 = np.arctan2(v1[1], v1[0])
    ang2 = np.arctan2(v2[1], v2[0])
    
    angle = ang2 - ang1
    if angle < 0:
        angle += 2 * np.pi
    return np.degrees(angle)

n = len(SPECTRE_POINTS)
angles = []
for i in range(n):
    p_prev = SPECTRE_POINTS[(i-1)%n]
    p_curr = SPECTRE_POINTS[i]
    p_next = SPECTRE_POINTS[(i+1)%n]
    angles.append(get_angle(p_next, p_curr, p_prev)) # Interior angle

print("Internal Angles of Spectre Tile (in degrees):")
for i, a in enumerate(angles):
    print(f"  v{i}: {a:.1f}°")

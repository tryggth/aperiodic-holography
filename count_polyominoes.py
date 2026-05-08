import math
import shapely
from shapely.geometry import Polygon
import numpy as np
import time
from collections import deque

SPECTRE_POINTS = [
    (0,                0),
    (1.0,              0.0),
    (1.5,              -np.sqrt(3)/2),
    (1.5+np.sqrt(3)/2, 0.5-np.sqrt(3)/2),
    (1.5+np.sqrt(3)/2, 1.5-np.sqrt(3)/2),
    (2.5+np.sqrt(3)/2, 1.5-np.sqrt(3)/2),
    (3+np.sqrt(3)/2,   1.5),
    (3.0,              2.0),
    (3-np.sqrt(3)/2,   1.5),
    (2.5-np.sqrt(3)/2, 1.5+np.sqrt(3)/2),
    (1.5-np.sqrt(3)/2, 1.5+np.sqrt(3)/2),
    (0.5-np.sqrt(3)/2, 1.5+np.sqrt(3)/2),
    (-np.sqrt(3)/2,    1.5),
    (0.0,              1.0)
]

base_poly = Polygon(SPECTRE_POINTS)

def transform_poly(poly, dx, dy, angle):
    import shapely.affinity
    p = shapely.affinity.rotate(poly, angle, use_radians=True, origin=(0,0))
    return shapely.affinity.translate(p, dx, dy)

# Precalculate the 116 valid neighbor relative poses
edges = []
for i in range(14):
    p1 = SPECTRE_POINTS[i]
    p2 = SPECTRE_POINTS[(i+1)%14]
    edges.append((p1, p2, math.atan2(p2[1] - p1[1], p2[0] - p1[0])))

valid_neighbors = []
for i in range(14):
    p1_a, p1_b, ang1 = edges[i]
    for j in range(14):
        p2_a, p2_b, ang2 = edges[j]
        rot_angle = ang1 + math.pi - ang2
        t2 = transform_poly(base_poly, 0, 0, rot_angle)
        p2_a_rot = t2.exterior.coords[j]
        dx = p1_b[0] - p2_a_rot[0]
        dy = p1_b[1] - p2_a_rot[1]
        
        t2_final = shapely.affinity.translate(t2, dx, dy)
        if base_poly.intersection(t2_final).area < 1e-5:
            # Check if they share exactly the edge
            valid_neighbors.append((dx, dy, rot_angle))

print(f"Valid neighbors for a single tile: {len(valid_neighbors)}")

# Pose: (x, y, theta) rounded to 3 decimals to avoid float issues
def get_pose(dx, dy, a):
    # normalize angle
    a = (a + math.pi) % (2*math.pi) - math.pi
    return (round(dx, 3), round(dy, 3), round(a, 3))

# Calculate absolute pose given parent pose and relative pose
def apply_relative(pose, rel):
    x, y, a = pose
    rx, ry, ra = rel
    # Rotate relative translation by parent angle
    c = math.cos(a)
    s = math.sin(a)
    nx = x + rx * c - ry * s
    ny = y + rx * s + ry * c
    na = a + ra
    return get_pose(nx, ny, na)

# Memoized overlap checking
overlap_cache = {}

def check_overlap(pose1, pose2):
    # To maximize cache hits, convert to relative pose from pose1 to pose2
    x1, y1, a1 = pose1
    x2, y2, a2 = pose2
    
    # Inverse of pose1
    c = math.cos(-a1)
    s = math.sin(-a1)
    dx = x2 - x1
    dy = y2 - y1
    rx = dx * c - dy * s
    ry = dx * s + dy * c
    ra = a2 - a1
    
    rel_key = get_pose(rx, ry, ra)
    if rel_key in overlap_cache:
        return overlap_cache[rel_key]
        
    p1 = transform_poly(base_poly, x1, y1, a1)
    p2 = transform_poly(base_poly, x2, y2, a2)
    
    over = p1.intersection(p2).area > 1e-5
    overlap_cache[rel_key] = over
    return over

def canonicalize(patch):
    # Find the lexicographically smallest set of poses under rigid rotation/translation
    # For a patch (set of poses), we can pick any tile as the origin.
    # We can also rotate it so its angle is 0.
    best = None
    for p_origin in patch:
        x0, y0, a0 = p_origin
        c = math.cos(-a0)
        s = math.sin(-a0)
        
        rel_poses = []
        for p in patch:
            x, y, a = p
            dx = x - x0
            dy = y - y0
            nx = dx * c - dy * s
            ny = dx * s + dy * c
            na = a - a0
            rel_poses.append(get_pose(nx, ny, na))
        
        canon = tuple(sorted(rel_poses))
        if best is None or canon < best:
            best = canon
    return best

def count_polyominoes(max_N):
    current_generation = { (get_pose(0,0,0),) }
    
    for n in range(2, max_N + 1):
        next_generation = set()
        print(f"Generating N={n}...")
        
        for patch in current_generation:
            # For each tile in the patch
            for i, parent_pose in enumerate(patch):
                # Try adding each valid neighbor
                for rel in valid_neighbors:
                    new_pose = apply_relative(parent_pose, rel)
                    
                    if new_pose in patch:
                        continue
                        
                    # Check overlap with ALL other tiles in patch
                    overlap = False
                    for other_pose in patch:
                        if check_overlap(new_pose, other_pose):
                            overlap = True
                            break
                            
                    if not overlap:
                        new_patch = list(patch) + [new_pose]
                        canon = canonicalize(new_patch)
                        next_generation.add(canon)
                        
        print(f"N={n}: {len(next_generation)} configurations")
        current_generation = next_generation

if __name__ == "__main__":
    count_polyominoes(4)

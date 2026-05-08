import math
import shapely
from shapely.geometry import Polygon
import numpy as np

# Coordinates of the Spectre tile
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

print("Base polygon area:", base_poly.area)

def transform_poly(poly, dx, dy, angle):
    # rotate by angle (radians), then translate by dx, dy
    # shapely rotate is in degrees, about origin (0,0) by default?
    import shapely.affinity
    p = shapely.affinity.rotate(poly, angle, use_radians=True, origin=(0,0))
    p = shapely.affinity.translate(p, dx, dy)
    return p

# For N=2, pick one edge of base_poly, and one edge of a new poly to align.
# Let's count N=2 without overlap.
edges = []
for i in range(14):
    p1 = SPECTRE_POINTS[i]
    p2 = SPECTRE_POINTS[(i+1)%14]
    dx = p2[0] - p1[0]
    dy = p2[1] - p1[1]
    angle = math.atan2(dy, dx)
    edges.append((p1, p2, angle))

valid_n2 = 0
for i in range(14):
    edge1 = edges[i]
    p1_a, p1_b, ang1 = edge1
    
    for j in range(14):
        # Align edge j of T2 to edge i of T1
        # edge j of T2 goes from p2_a to p2_b with angle ang2
        # We want p2_b to map to p1_a and p2_a to map to p1_b
        # So the new angle is ang1 + pi
        edge2 = edges[j]
        ang2 = edge2[2]
        
        rot_angle = ang1 + math.pi - ang2
        
        # apply rot_angle to T2
        t2 = transform_poly(base_poly, 0, 0, rot_angle)
        
        # now edge j of t2 starts at p2_a_rotated.
        # we want to translate it to p1_b.
        p2_a_rot = t2.exterior.coords[j]
        
        dx = p1_b[0] - p2_a_rot[0]
        dy = p1_b[1] - p2_a_rot[1]
        
        t2_final = shapely.affinity.translate(t2, dx, dy)
        
        # Check overlap
        intersection = base_poly.intersection(t2_final)
        if intersection.area < 1e-5:
            valid_n2 += 1

print("Valid N=2 configurations:", valid_n2)


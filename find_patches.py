import json
import random
import numpy as np
import time

IDENTITY = [1, 0, 0, 0, 1, 0]

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

def mul(A, B):
    return [
        A[0]*B[0] + A[1]*B[3],
        A[0]*B[1] + A[1]*B[4],
        A[0]*B[2] + A[1]*B[5] + A[2],

        A[3]*B[0] + A[4]*B[3],
        A[3]*B[1] + A[4]*B[4],
        A[3]*B[2] + A[4]*B[5] + A[5]
    ]

def trot(ang):
    c = np.cos(ang)
    s = np.sin(ang)
    return [c, -s, 0, s, c, 0]

def ttrans(tx, ty):
    return [1, 0, tx, 0, 1, ty]

def transTo(p, q):
    return ttrans(q.x - p.x, q.y - p.y)

def transPt(M, P):
    return pt(M[0]*P.x + M[1]*P.y + M[2], M[3]*P.x + M[4]*P.y + M[5])

class Tile:
    def __init__(self, pts, label):
        self.quad = [pts[3], pts[5], pts[7], pts[11]]
        self.label = label

class MetaTile:
    def __init__(self, geometries=[], quad=[]):
        self.geometries = geometries
        self.quad = quad

def buildSpectreBase():
    TILE_NAMES = ["Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Phi", "Psi"]
    spectre_base_cluster = { label: Tile(SPECTRE_POINTS, label) for label in TILE_NAMES if label != "Gamma" }
    mystic = MetaTile(
        [
            [Tile(SPECTRE_POINTS, "Gamma1"), IDENTITY],
            [Tile(SPECTRE_POINTS, "Gamma2"), mul(ttrans(SPECTRE_POINTS[8].x, SPECTRE_POINTS[8].y), trot(np.pi/6))]
        ],
        [SPECTRE_POINTS[3], SPECTRE_POINTS[5], SPECTRE_POINTS[7], SPECTRE_POINTS[11]]
    )
    spectre_base_cluster["Gamma"] = mystic
    return spectre_base_cluster

def buildSupertiles(tileSystem):
    quad = tileSystem["Delta"].quad
    R = [-1, 0, 0, 0, 1, 0]

    transformation_rules = [
        [60, 3, 1], [0, 2, 0], [60, 3, 1], [60, 3, 1],
        [0, 2, 0], [60, 3, 1], [-120, 3, 3]
    ]

    transformations = [IDENTITY]
    total_angle = 0
    rotation = IDENTITY
    transformed_quad = list(quad)

    for _angle, _from, _to in transformation_rules:
        if(_angle != 0):
            total_angle += _angle
            rotation = trot(np.deg2rad(total_angle))
            transformed_quad = [ transPt(rotation, quad_pt) for quad_pt in quad ]

        ttt = transTo(
            transformed_quad[_to],
            transPt(transformations[-1], quad[_from])
        )
        transformations.append(mul(ttt, rotation))

    transformations = [ mul(R, transformation) for transformation in transformations ]

    super_rules = {
        "Gamma":  ["Pi",  "Delta", None,  "Theta", "Sigma", "Xi",  "Phi",    "Gamma"],
        "Delta":  ["Xi",  "Delta", "Xi",  "Phi",   "Sigma", "Pi",  "Phi",    "Gamma"],
        "Theta":  ["Psi", "Delta", "Pi",  "Phi",   "Sigma", "Pi",  "Phi",    "Gamma"],
        "Lambda": ["Psi", "Delta", "Xi",  "Phi",   "Sigma", "Pi",  "Phi",    "Gamma"],
        "Xi":     ["Psi", "Delta", "Pi",  "Phi",   "Sigma", "Psi", "Phi",    "Gamma"],
        "Pi":     ["Psi", "Delta", "Xi",  "Phi",   "Sigma", "Psi", "Phi",    "Gamma"],
        "Sigma":  ["Xi",  "Delta", "Xi",  "Phi",   "Sigma", "Pi",  "Lambda", "Gamma"],
        "Phi":    ["Psi", "Delta", "Psi", "Phi",   "Sigma", "Pi",  "Phi",    "Gamma"],
        "Psi":    ["Psi", "Delta", "Psi", "Phi",   "Sigma", "Psi", "Phi",    "Gamma"]
    }
    super_quad = [
        transPt(transformations[6], quad[2]),
        transPt(transformations[5], quad[1]),
        transPt(transformations[3], quad[2]),
        transPt(transformations[0], quad[1])
    ]

    return {
        label: MetaTile(
            [ [tileSystem[sub], transform] for sub, transform in zip(substitutions, transformations) if sub ],
            super_quad
        ) for label, substitutions in super_rules.items() }

def get_base_tiles(item, current_transform=IDENTITY):
    tiles = []
    if isinstance(item, Tile):
        points = [transPt(current_transform, p) for p in SPECTRE_POINTS]
        # Round coords to 5 decimals to avoid floating point issues
        coords = [ (round(p.x, 5), round(p.y, 5)) for p in points ]
        tiles.append(coords)
    elif isinstance(item, MetaTile):
        for sub_item, transform in item.geometries:
            tiles.extend(get_base_tiles(sub_item, mul(current_transform, transform)))
    return tiles

def sample_patch(adjacency, n_tiles, max_size):
    size = random.randint(1, max_size)
    start_tile = random.randint(0, n_tiles - 1)
    patch = {start_tile}
    neighbors = set(adjacency[start_tile])
    while len(patch) < size and neighbors:
        next_tile = random.choice(list(neighbors))
        patch.add(next_tile)
        neighbors.remove(next_tile)
        for n in adjacency[next_tile]:
            if n not in patch:
                neighbors.add(n)
    return frozenset(patch)

def get_boundary_ordered(patch, tile_edges):
    # Collect all edges for tiles in the patch
    edge_counts = {}
    for t in patch:
        for e in tile_edges[t]:
            edge_counts[e] = edge_counts.get(e, 0) + 1
            
    # Boundary edges are those that appear exactly once
    boundary_edges = [e for e, count in edge_counts.items() if count == 1]
    
    # Graph of boundary vertices
    b_graph = {}
    for e in boundary_edges:
        u, v = list(e)
        if u not in b_graph: b_graph[u] = []
        if v not in b_graph: b_graph[v] = []
        b_graph[u].append(v)
        b_graph[v].append(u)
        
    # Check degrees
    for u, neighbors in b_graph.items():
        if len(neighbors) != 2:
            return None # Not a simple cycle
            
    # Check connectivity and order vertices
    if not b_graph: return None
    
    start_node = next(iter(b_graph.keys()))
    ordered = [start_node]
    curr = b_graph[start_node][0]
    prev = start_node
    
    while curr != start_node:
        ordered.append(curr)
        # Find next
        neighbors = b_graph[curr]
        next_node = neighbors[0] if neighbors[0] != prev else neighbors[1]
        prev = curr
        curr = next_node
        
    if len(ordered) != len(b_graph):
        return None # Multiple disconnected cycles (means it has holes)
        
    return ordered

def main():
    print("Generating Mystic-4 supertile...")
    start_time = time.time()
    shapes = buildSpectreBase()
    for _ in range(3):
        shapes = buildSupertiles(shapes)
        
    tiles = get_base_tiles(shapes["Gamma"])
    print(f"Generated {len(tiles)} base tiles in {time.time() - start_time:.2f} seconds.")

    print("Building adjacency graph...")
    tile_edges = []
    edge_to_tiles = {}
    for i, t in enumerate(tiles):
        # The vertices are ordered around the perimeter, so edges are consecutive pairs
        edges = [frozenset([t[j], t[(j+1)%14]]) for j in range(14)]
        tile_edges.append(edges)
        for e in edges:
            if e not in edge_to_tiles:
                edge_to_tiles[e] = []
            edge_to_tiles[e].append(i)

    adjacency = {i: set() for i in range(len(tiles))}
    for e, t_list in edge_to_tiles.items():
        if len(t_list) == 2:
            u, v = t_list
            adjacency[u].add(v)
            adjacency[v].add(u)
            
    print("Sampling patches...")
    found_boundaries = []
    seen_patches = set()
    attempts = 0
    
    # We want a variety of sizes
    MAX_PATCH_SIZE = 100
    
    random.seed(42) # For reproducibility
    
    while len(found_boundaries) < 1000:
        attempts += 1
        patch = sample_patch(adjacency, len(tiles), MAX_PATCH_SIZE)
        if patch in seen_patches:
            continue
        seen_patches.add(patch)
        
        ordered_boundary = get_boundary_ordered(patch, tile_edges)
        if ordered_boundary is not None:
            found_boundaries.append({
                "patch_size": len(patch),
                "boundary": ordered_boundary
            })
            if len(found_boundaries) % 100 == 0:
                print(f"Found {len(found_boundaries)} simply connected patches (attempts: {attempts})...")
                
    print(f"Done! Saving to mystic_4_boundaries.json")
    with open("mystic_4_boundaries.json", "w") as f:
        json.dump(found_boundaries, f, indent=2)

if __name__ == "__main__":
    main()

import json
import random
import math
import time
import numpy as np
from collections import defaultdict

# --- Spectre tile generation logic ---
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
        A[0]*B[0] + A[1]*B[3], A[0]*B[1] + A[1]*B[4], A[0]*B[2] + A[1]*B[5] + A[2],
        A[3]*B[0] + A[4]*B[3], A[3]*B[1] + A[4]*B[4], A[3]*B[2] + A[4]*B[5] + A[5]
    ]

def trot(ang):
    c, s = np.cos(ang), np.sin(ang)
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
    mystic = MetaTile([
        [Tile(SPECTRE_POINTS, "Gamma1"), IDENTITY],
        [Tile(SPECTRE_POINTS, "Gamma2"), mul(ttrans(SPECTRE_POINTS[8].x, SPECTRE_POINTS[8].y), trot(np.pi/6))]
    ], [SPECTRE_POINTS[3], SPECTRE_POINTS[5], SPECTRE_POINTS[7], SPECTRE_POINTS[11]])
    spectre_base_cluster["Gamma"] = mystic
    return spectre_base_cluster

def buildSupertiles(tileSystem):
    quad = tileSystem["Delta"].quad
    R = [-1, 0, 0, 0, 1, 0]
    transformation_rules = [[60, 3, 1], [0, 2, 0], [60, 3, 1], [60, 3, 1], [0, 2, 0], [60, 3, 1], [-120, 3, 3]]
    transformations = [IDENTITY]
    total_angle = 0
    rotation = IDENTITY
    transformed_quad = list(quad)

    for _angle, _from, _to in transformation_rules:
        if(_angle != 0):
            total_angle += _angle
            rotation = trot(np.deg2rad(total_angle))
            transformed_quad = [ transPt(rotation, qp) for qp in quad ]
        ttt = transTo(transformed_quad[_to], transPt(transformations[-1], quad[_from]))
        transformations.append(mul(ttt, rotation))
    transformations = [ mul(R, t) for t in transformations ]

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
        transPt(transformations[6], quad[2]), transPt(transformations[5], quad[1]),
        transPt(transformations[3], quad[2]), transPt(transformations[0], quad[1])
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
        # Coordinates rounded to avoid float issues in edge building
        coords = [ (round(p.x, 5), round(p.y, 5)) for p in points ]
        tiles.append(coords)
    elif isinstance(item, MetaTile):
        for sub_item, transform in item.geometries:
            tiles.extend(get_base_tiles(sub_item, mul(current_transform, transform)))
    return tiles

# --- Graph and Analysis logic ---

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

def get_boundary_info(patch, tile_edges):
    edge_counts = {}
    for t in patch:
        for e in tile_edges[t]:
            edge_counts[e] = edge_counts.get(e, 0) + 1
            
    boundary_edges = [e for e, count in edge_counts.items() if count == 1]
    
    b_graph = {}
    for e in boundary_edges:
        u, v = list(e)
        if u not in b_graph: b_graph[u] = []
        if v not in b_graph: b_graph[v] = []
        b_graph[u].append(v)
        b_graph[v].append(u)
        
    for u, neighbors in b_graph.items():
        if len(neighbors) != 2:
            return None, None
            
    if not b_graph: return None, None
    
    start_node = next(iter(b_graph.keys()))
    ordered = [start_node]
    curr = b_graph[start_node][0]
    prev = start_node
    
    while curr != start_node:
        ordered.append(curr)
        neighbors = b_graph[curr]
        next_node = neighbors[0] if neighbors[0] != prev else neighbors[1]
        prev = curr
        curr = next_node
        
    if len(ordered) != len(b_graph):
        return None, None
        
    m = len(ordered)
    turns = []
    for i in range(m):
        p_prev = ordered[i-1]
        p_curr = ordered[i]
        p_next = ordered[(i+1)%m]
        
        angle_in = math.degrees(math.atan2(p_curr[1] - p_prev[1], p_curr[0] - p_prev[0]))
        angle_out = math.degrees(math.atan2(p_next[1] - p_curr[1], p_next[0] - p_curr[0]))
        
        diff = (angle_out - angle_in + 180) % 360 - 180
        if diff == -180: diff = 180
        turn = int(round(diff / 30.0) * 30)
        turns.append(turn)
        
    return ordered, turns

def get_canonical_alignments(turns):
    n = len(turns)
    best = tuple(turns)
    best_indices = [0]
    for i in range(1, n):
        shifted = tuple(turns[i:] + turns[:i])
        if shifted < best:
            best = shifted
            best_indices = [i]
        elif shifted == best:
            best_indices.append(i)
    return best, best_indices

def transform_point(p, v_start, neg_alpha):
    tx = p[0] - v_start[0]
    ty = p[1] - v_start[1]
    c = math.cos(neg_alpha)
    s = math.sin(neg_alpha)
    nx = tx * c - ty * s
    ny = tx * s + ty * c
    return (nx, ny)

def get_internal_hash(patch_tiles, v_start, neg_alpha):
    transformed_tiles = []
    for tile in patch_tiles:
        t_tile = [transform_point(p, v_start, neg_alpha) for p in tile]
        # Sort rounded vertices to uniquely fingerprint a tile shape/position
        rounded_tile = tuple(sorted((round(p[0], 3), round(p[1], 3)) for p in t_tile))
        transformed_tiles.append(rounded_tile)
    # Sort all tiles so the set is canonical
    transformed_tiles.sort()
    return tuple(transformed_tiles)

def main():
    print("Generating Mystic-4 geometry...")
    t0 = time.time()
    shapes = buildSpectreBase()
    for _ in range(3):
        shapes = buildSupertiles(shapes)
    tiles = get_base_tiles(shapes["Gamma"])
    
    tile_edges = []
    edge_to_tiles = {}
    for i, t in enumerate(tiles):
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
            
    print(f"Setup complete in {time.time()-t0:.2f}s")
    
    TARGET_PATCHES = 5000
    MAX_PATCH_SIZE = 100
    seen_patches = set()
    found_patches = 0
    
    # Map: canon_boundary_hash -> list of (internal_hash, patch_size)
    boundary_to_internals = defaultdict(list)
    
    random.seed(42)
    print(f"Sampling {TARGET_PATCHES} simply connected patches...")
    
    start_time = time.time()
    attempts = 0
    
    while found_patches < TARGET_PATCHES:
        attempts += 1
        patch = sample_patch(adjacency, len(tiles), MAX_PATCH_SIZE)
        if patch in seen_patches:
            continue
        seen_patches.add(patch)
        
        ordered_verts, turns = get_boundary_info(patch, tile_edges)
        if ordered_verts is None:
            continue # not simply connected
            
        found_patches += 1
        if found_patches % 500 == 0:
            print(f"  Found {found_patches} / {TARGET_PATCHES} (attempts: {attempts})")
            
        canon_turns, indices = get_canonical_alignments(turns)
        patch_tiles_data = [tiles[t] for t in patch]
        
        best_internal_hash = None
        for idx in indices:
            v_start = ordered_verts[idx]
            v_end = ordered_verts[(idx+1)%len(ordered_verts)]
            alpha = math.atan2(v_end[1] - v_start[1], v_end[0] - v_start[0])
            neg_alpha = -alpha
            
            ihash = get_internal_hash(patch_tiles_data, v_start, neg_alpha)
            if best_internal_hash is None or ihash < best_internal_hash:
                best_internal_hash = ihash
                
        boundary_to_internals[canon_turns].append((best_internal_hash, len(patch)))

    total_time = time.time() - start_time
    print(f"\nProcessing {TARGET_PATCHES} patches took {total_time:.2f} seconds.")
    # Estimate total simply connected patches: ~10k?
    # Wait, the number of connected subgraphs of max size 100 on 488 nodes is astronomically large.
    # The user asked: "calculate how long it would take to do all connected sub patches of Mystic-4."
    
    print("\n--- Collision Analysis ---")
    multiple_occurrences = 0
    counter_examples = 0
    
    for b_hash, internal_list in boundary_to_internals.items():
        if len(internal_list) > 1:
            multiple_occurrences += 1
            # Check if all internal hashes are identical
            first_hash = internal_list[0][0]
            for ihash, size in internal_list[1:]:
                if ihash != first_hash:
                    counter_examples += 1
                    print(f"!!! COUNTER-EXAMPLE FOUND !!!")
                    print(f"Boundary of length {len(b_hash)} has multiple valid non-isomorphic internal tilings!")
                    break
                    
    print(f"Total unique boundary shapes: {len(boundary_to_internals)}")
    print(f"Boundary shapes appearing multiple times (collisions): {multiple_occurrences}")
    print(f"Number of counter-examples (isomorphic boundaries, different internal tilings): {counter_examples}")
    
    if counter_examples == 0:
        print("\nAll tested patches strongly obey the theorem: Internal tilings are rigidly isomorphic when their boundary shapes match.")

if __name__ == "__main__":
    main()

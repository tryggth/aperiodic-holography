import json
import math

def calculate_angle_distance(p1, p2):
    dx = p2[0] - p1[0]
    dy = p2[1] - p1[1]
    
    # Calculate distance
    dist = math.sqrt(dx**2 + dy**2)
    # The edges are length 1, but let's round to nearest integer
    # (Since there are no other valid distances)
    rounded_dist = int(round(dist))
    
    # Calculate angle in degrees
    angle_rad = math.atan2(dy, dx)
    angle_deg = math.degrees(angle_rad)
    
    # Round to nearest multiple of 30
    rounded_angle = int(round(angle_deg / 30.0) * 30) % 360
    
    return rounded_angle, rounded_dist

def main():
    with open("mystic_4_boundaries.json", "r") as f:
        data = json.load(f)
        
    new_data = []
    
    for i, patch in enumerate(data, start=1):
        coords = patch["boundary"]
        n = len(coords)
        
        new_boundary = []
        for j in range(n):
            # Previous point (wraps around)
            p_prev = coords[j-1]
            p_curr = coords[j]
            
            angle, dist = calculate_angle_distance(p_prev, p_curr)
            
            new_boundary.append({
                "angle": angle,
                "distance": dist
            })
            
        new_data.append({
            "patch_id": i,
            "patch_size": patch["patch_size"],
            "boundary": new_boundary
        })
        
    with open("mystic_4_boundaries_transformed.json", "w") as f:
        json.dump(new_data, f, indent=2)
        
if __name__ == "__main__":
    main()

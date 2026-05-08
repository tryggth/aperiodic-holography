import json

def get_turn_angle(prev_a, curr_a):
    diff = (curr_a - prev_a + 180) % 360 - 180
    if diff == -180:
        diff = 180
    return diff

def main():
    with open("mystic_4_boundaries_transformed.json", "r") as f:
        data = json.load(f)
        
    for patch in data:
        boundary = patch["boundary"]
        n = len(boundary)
        new_boundary = []
        
        for i in range(n):
            in_edge = boundary[i]
            out_edge = boundary[(i+1)%n]
            
            turn = get_turn_angle(in_edge["angle"], out_edge["angle"])
            dist = out_edge["distance"]
            
            new_boundary.append({
                "turn_angle": turn,
                "distance": dist
            })
            
        patch["boundary"] = new_boundary
        
    with open("mystic_4_boundaries_turning.json", "w") as f:
        json.dump(data, f, indent=2)

if __name__ == "__main__":
    main()

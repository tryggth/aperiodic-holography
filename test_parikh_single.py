import json
import math

def angle_to_idx(ang):
    return int(round(ang / 30.0)) % 12

def main():
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    for p in data:
        if p["patch_size"] == 1:
            turns = [e["turn_angle"] for e in p["boundary"]]
            
            abs_angles = []
            curr = 0
            for t in turns:
                curr = (curr + t) % 360
                abs_angles.append(curr)
                
            vec6 = [0]*6
            for a in abs_angles:
                vec6[angle_to_idx(a) % 6] += 1
                
            print("Size 1 tile 6D:", vec6)
            print("Size 1 tile mod 2:", [x % 2 for x in vec6])
            break
            
if __name__ == "__main__":
    main()

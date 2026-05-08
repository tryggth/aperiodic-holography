import json
from collections import Counter

def main():
    with open("mystic_4_boundaries_turning.json", "r") as f:
        data = json.load(f)
        
    sum_turns = set()
    lengths = set()
    turn_values = set()
    
    # Let's count turn angles
    all_turns_counter = Counter()
    
    # Let's check pairs of turns
    pair_counter = Counter()

    for patch in data:
        boundary = patch["boundary"]
        
        # 1. Sum of turns
        total_turn = sum(edge["turn_angle"] for edge in boundary)
        sum_turns.add(total_turn)
        
        # 2. Length of boundary
        lengths.add(len(boundary))
        
        # 3. Values of turns
        turns = [edge["turn_angle"] for edge in boundary]
        for t in turns:
            turn_values.add(t)
            all_turns_counter[t] += 1
            
        # 4. Pairs of turns
        for i in range(len(turns)):
            pair = (turns[i], turns[(i+1)%len(turns)])
            pair_counter[pair] += 1

    print("Sum of turning angles:", sum_turns)
    print("Unique boundary lengths modulo 2:", set(l % 2 for l in lengths))
    print("Allowed turn angles:", sorted(list(turn_values)))
    
    print("\nTurn Angle Frequencies (across all patches):")
    for k, v in sorted(all_turns_counter.items()):
        print(f"  {k:4d}: {v}")
        
    print("\nTop 5 Most Common Turn Pairs:")
    for k, v in pair_counter.most_common(5):
        print(f"  {k}: {v}")
        
    print("\nAre there any 180 degree turns?", 180 in turn_values or -180 in turn_values)

if __name__ == "__main__":
    main()

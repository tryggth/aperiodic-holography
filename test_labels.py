import math
import matplotlib.pyplot as plt

xs, ys = [0], [0]
heading = 0
turns = [60, 0, 90, 30, 120, 60, 330, 270, 0, 330, 240, 270, 180, 210]

for turn in turns:
    heading = (heading + turn) % 360
    rad = math.radians(heading)
    xs.append(xs[-1] + math.cos(rad))
    ys.append(ys[-1] + math.sin(rad))

M = len(xs) - 1
print(f"M={M}")
for i in range(M):
    label_idx = (-i) % M 
    print(f"Point {i}: ({xs[i]:.2f}, {ys[i]:.2f}) gets label v{label_idx}")

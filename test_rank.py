import numpy as np

# A single tile unrotated has 6D Parikh vector:
v0 = np.array([2, 2, 2, 2, 4, 2])

# When rotated by 30 degrees (1 step), the directions shift circularly.
# So v1 is a cyclic permutation of v0.
vectors = []
for i in range(6):
    # cyclic shift right by i
    v = np.roll(v0, i)
    vectors.append(v)

M = np.array(vectors)
print("Matrix of tile vectors (6 orientations):")
print(M)
print("Rank:", np.linalg.matrix_rank(M))

# Let's find the nullspace
from scipy.linalg import null_space
ns = null_space(M)
print("Nullspace:")
print(np.round(ns, 3))

# Wait, Parikh vectors are independent of translation, but dependent on rotation.
# The 6 vectors span the space of tile Parikh vectors.
# Rank is 6! So the span is all of R^6.

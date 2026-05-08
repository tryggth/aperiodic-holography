import numpy as np

v0 = np.array([2, 2, 2, 2, 4, 2])
vectors = [np.roll(v0, i) for i in range(6)]
M = np.array(vectors)

# determinant
d = int(round(np.linalg.det(M)))
print("Determinant of M:", d)

# Let's find the Smith Normal Form or at least eigenvalues
try:
    import sympy
    from sympy import Matrix
    M_sym = Matrix(M)
    snf = M_sym.smith_normal_form()
    print("Smith Normal Form:")
    print(snf)
    print("Diagonal elements:", [snf[i,i] for i in range(6)])
except Exception as e:
    print(e)

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Spectrebound.SpectreFatgraph

/-!
  SPECTREBOUND: CELLULAR SHEAF MODULE
  
  This module linearizes the Spectre boundary matching rules into matrix
  transformations over a finite field (ZMod p). 
  
  By framing the tiling layout as a Discrete Dirichlet Boundary Value Problem, 
  we can prove Holographic Uniqueness: if the boundary sequence is fixed, 
  the determinant of the interior block matrix guarantees exactly one valid 
  bulk configuration.
-/
namespace Spectrebound

/-- We evaluate our linear algebra over a finite field. 
    Using a prime field ensures we have a division ring where non-zero 
    determinants guarantee invertible matrices. -/
abbrev CoefficientField (p : Nat) [Fact p.Prime] := ZMod p

/-- The vector space representing the state (orientation/placement) of a single tile. -/
abbrev TileState (p : Nat) [Fact p.Prime] (n : Nat) := Fin n → CoefficientField p

/-- The incidence matrix defining the structural constants (matching rules) 
    between adjacent tiles. -/
abbrev LocalGluingMatrix (p : Nat) [Fact p.Prime] (rows cols : Nat) := 
  Matrix (Fin rows) (Fin cols) (CoefficientField p)

/-- The Global Gluing Differential. 
    A tiling patch is valid if and only if its state vector `s` sits in the 
    kernel of this matrix: D * s = 0. -/
structure GluingDifferential (p : Nat) [Fact p.Prime] (n_edges n_tiles : Nat) where
  D : Matrix (Fin n_edges) (Fin n_tiles) (CoefficientField p)

/-- To solve the Dirichlet problem, we partition the global matrix into 
    the internal 'Bulk' and the external 'Boundary'. -/
structure DirichletPartition (p : Nat) [Fact p.Prime] (n_bulk n_bdry : Nat) where
  D_bulk : Matrix (Fin n_bulk) (Fin n_bulk) (CoefficientField p)
  D_bdry : Matrix (Fin n_bulk) (Fin n_bdry) (CoefficientField p)
  -- The Holographic Uniqueness property: The bulk matrix is non-singular.
  -- This guarantees D_bulk * s_bulk = -D_bdry * s_bdry has a unique solution.
  det_nonzero : D_bulk.det ≠ 0

end Spectrebound

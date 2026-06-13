import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Spectrebound.SpectreFatgraph

/-!
  SPECTREBOUND: FIBER BUNDLE MODULE
  
  This module linearizes the Spectre boundary matching rules into matrix
  transformations over a finite field (ZMod p), acting as a discrete 
  Vector Bundle over our Combinatorial Surface.
-/
namespace Spectrebound

/-- The finite field coefficient space. -/
abbrev StateField (p : Nat) [Fact p.Prime] := ZMod p

/-- The vector space representing the state of a single tile (Fiber). -/
abbrev LocalFiber (p : Nat) [Fact p.Prime] (n : Nat) := Fin n → StateField p

/-- The incidence matrix defining the connection between adjacent fibers. -/
abbrev ConnectionComponent (p : Nat) [Fact p.Prime] (rows cols : Nat) := 
  Matrix (Fin rows) (Fin cols) (StateField p)

/-- The global Covariant Derivative. A valid tiling patch is a Parallel Section 
    sitting in the kernel: D * s = 0. -/
structure HolonomicConnection (p : Nat) [Fact p.Prime] (n_edges n_tiles : Nat) where
  D : Matrix (Fin n_edges) (Fin n_tiles) (StateField p)

/-- The Classical Boundary Value Problem. -/
structure DirichletForcing (p : Nat) [Fact p.Prime] (n_bulk n_bdry : Nat) where
  D_bulk : Matrix (Fin n_bulk) (Fin n_bulk) (StateField p)
  D_bdry : Matrix (Fin n_bulk) (Fin n_bdry) (StateField p)
  det_nonzero : D_bulk.det ≠ 0

end Spectrebound

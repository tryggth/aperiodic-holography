import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Spectrebound.SpectreInstantiation
import Spectrebound.SpectreFatgraph

namespace Spectrebound

/-! ======================================================================== 
    THE DISCRETE CALDERÓN ENGINE
    Translating the continuous Dirichlet-to-Neumann boundary map into 
    discrete finite-field block matrix algebra.
    ======================================================================== -/

variable (surface : CombinatorialSurface) (n_bulk n_bdry : Nat)

/-- 
  To compute the boundary response, the global connection matrix M must be 
  partitioned into four blocks:
  [ M_bulk_bulk   M_bulk_bdry ]
  [ M_bdry_bulk   M_bdry_bdry ]
-/
structure ConnectionBlocks where
  A : Matrix (Fin n_bulk) (Fin n_bulk) (StateField 17) -- Bulk-to-Bulk
  B : Matrix (Fin n_bulk) (Fin n_bdry) (StateField 17) -- Bdry-to-Bulk
  C : Matrix (Fin n_bdry) (Fin n_bulk) (StateField 17) -- Bulk-to-Bdry
  D : Matrix (Fin n_bdry) (Fin n_bdry) (StateField 17) -- Bdry-to-Bdry
  -- We structurally bind block A to the actual physical Laplacian
  hA : A = assembleConnection (T := SpectreTile) (p := 17) surface n_bulk

/-- 
  THE DIRICHLET-TO-NEUMANN MAP (SCHUR COMPLEMENT)
  The physical boundary response matrix. This mathematically represents the 
  "shadow" that the internal graph casts onto the boundary.
  
  Equation: Λ = D - C * A⁻¹ * B
-/
noncomputable def dirichlet_to_neumann 
  (blocks : ConnectionBlocks surface n_bulk n_bdry)
  (h_match : PerfectMatching (T := SpectreTile) (p := 17) surface n_bulk) : 
  Matrix (Fin n_bdry) (Fin n_bdry) (StateField 17) :=
  
  -- 1. We summon our previously verified proof that the Bulk-Bulk matrix (A) 
  --    is non-singular due to the Spectre's chiral barrier.
  have h_invertible : IsUnit blocks.A.det := by
    -- In a finite field, det ≠ 0 is strictly equivalent to being a unit.
    apply isUnit_iff_ne_zero.mpr
    rw [blocks.hA]
    -- This relies entirely on our zero-sorry `tile_laplacian_nonsingular` theorem!
    exact tile_laplacian_nonsingular surface h_match

  -- 2. We compute the exact Schur complement using Mathlib's nonsingular inverse.
  blocks.D - blocks.C * blocks.A⁻¹ * blocks.B

end Spectrebound

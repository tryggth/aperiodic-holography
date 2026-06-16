import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Spectrebound.SpectreFatgraph
import Spectrebound.SpectreCalderon
import Spectrebound.SpectreInstantiation

namespace Spectrebound

/-! ======================================================================== 
    INVERSE FINITE-FIELD NETWORK TOMOGRAPHY (THE "PHD THESIS")
    ======================================================================== -/

variable {p : Nat} [Fact p.Prime] (surface : CombinatorialSurface) (n_bulk n_bdry : Nat)

/-! ========================================================================
  PHASE 1: THE Y-Δ (STAR-MESH) TRANSFORM
  ======================================================================== -/

structure StarNode (F : Type) [Field F] where
  a : F
  b : F
  c : F

structure MeshTriangle (F : Type) [Field F] where
  A : F
  B : F
  C : F

def star_to_mesh {F : Type} [Field F] (star : StarNode F) (h_sum : star.a + star.b + star.c ≠ 0) : MeshTriangle F := {
  A := (star.b * star.c) / (star.a + star.b + star.c),
  B := (star.a * star.c) / (star.a + star.b + star.c),
  C := (star.a * star.b) / (star.a + star.b + star.c)
}

/-! ========================================================================
  PHASE 2: THE HOLONOMIC TENSOR UPGRADE
  Upgrading the 1D dipole matrix into a true 2D 3-regular network.
  ======================================================================== -/

/-- The Counter-Clockwise Face Permutation (Reverse of face_next). -/
def face_prev (d : DartId) : DartId :=
  (d / 14) * 14 + (d + 13) % 14

/-- 
  THE 2D TENSOR CONNECTION
  Unlike the 1D assembleConnection, this matrix connects darts both across 
  glued boundaries AND along the internal faces of the tiles. 
  Every dart is now a degree-3 node (a Star configuration).
-/
def tensorConnection [tile : HolonomicTile SpectreTile 17] (n : Nat) : 
  Matrix (Fin n) (Fin n) (StateField 17) :=
  fun i j =>
    if i == j then 1 
    else if isGlued surface.ledger i.val j.val then tile.getPhase i.val 
    else if j.val == face_next i.val then 1  -- Face propagation (forward)
    else if j.val == face_prev i.val then 1  -- Face propagation (backward)
    else 0

end Spectrebound

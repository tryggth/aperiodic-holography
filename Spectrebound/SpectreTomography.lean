import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Spectrebound.SpectreFatgraph
import Spectrebound.SpectreCalderon
import Spectrebound.SpectreInstantiation

namespace Spectrebound

/-! ======================================================================== 
    INVERSE FINITE-FIELD NETWORK TOMOGRAPHY (THE "PHD THESIS")
    ======================================================================== -/

variable {p : Nat} [Fact p.Prime] (surface : CombinatorialSurface) (n_bulk n_bdry : Nat)

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
  ======================================================================== -/

def face_prev (d : DartId) : DartId :=
  (d / 14) * 14 + (d + 13) % 14

def tensorConnection [tile : HolonomicTile SpectreTile 17] (n : Nat) : 
  Matrix (Fin n) (Fin n) (StateField 17) :=
  fun i j =>
    if i == j then 1 
    else if isGlued surface.ledger i.val j.val then tile.getPhase i.val 
    else if j.val == face_next i.val then 1
    else if j.val == face_prev i.val then 1
    else 0

/-! ========================================================================
  PHASE 3: DYNAMIC SINGULARITY AVOIDANCE
  To handle the physical "Dart 9 Singularity" (1 + 1 + 15 = 17 ≡ 0), we must 
  construct a safe evaluator that utilizes Decidable equality to return `none` 
  if a node is currently singular, allowing the tomography algorithm to route 
  around it and reduce neighboring nodes first.
  ======================================================================== -/

/-- 
  A safe wrapper around `star_to_mesh`. 
  If the sum of the incident weights is exactly 0, it aborts the transform.
  If the sum is non-zero, it executes the strict mathematical reduction.
-/
def safe_star_to_mesh {F : Type} [Field F] [DecidableEq F] (star : StarNode F) : Option (MeshTriangle F) :=
  if h : star.a + star.b + star.c = 0 then
    none -- Node is singular (e.g., Dart 9 before neighbor reduction). Skip and reschedule.
  else
    some (star_to_mesh star h)

end Spectrebound

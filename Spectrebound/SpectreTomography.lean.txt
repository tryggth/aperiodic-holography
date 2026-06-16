import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Spectrebound.SpectreFatgraph
import Spectrebound.SpectreCalderon
import Spectrebound.SpectreInstantiation
import Mathlib.Data.List.FinRange

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

-- Prefixed _h_sum to silence the unused proof parameter linter
def star_to_mesh {F : Type} [Field F] (star : StarNode F) (_h_sum : star.a + star.b + star.c ≠ 0) : MeshTriangle F := {
  A := (star.b * star.c) / (star.a + star.b + star.c),
  B := (star.a * star.c) / (star.a + star.b + star.c),
  C := (star.a * star.b) / (star.a + star.b + star.c)
}

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

def safe_star_to_mesh {F : Type} [Field F] [DecidableEq F] (star : StarNode F) : Option (MeshTriangle F) :=
  if h : star.a + star.b + star.c = 0 then none 
  else some (star_to_mesh star h)

/-! ========================================================================
  PHASE 5: THE MATRIX SUPERPOSITION ENGINE
  Dynamically reading and mutating the weights of the evolving tensor network.
  ======================================================================== -/

/-- Dynamically locates the active non-zero neighbors of a given node in the matrix. -/
def active_neighbors (n : Nat) (W : Matrix (Fin n) (Fin n) (StateField 17)) (k : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun j => k ≠ j ∧ W k j ≠ 0)

/-- Extracts the 3 incident weights of a dynamically routed degree-3 node. -/
def extract_star (n : Nat) (W : Matrix (Fin n) (Fin n) (StateField 17)) (k : Fin n) : StarNode (StateField 17) :=
  match active_neighbors n W k with
  | [n1, n2, n3] => { a := W k n1, b := W k n2, c := W k n3 }
  | _ => { a := 0, b := 0, c := 0 } -- Fallback gracefully if node degree dynamically shifts

/-- 
  Injects the new Delta mesh weights via superposition (matrix addition) 
  and mathematically annihilates the marginalized target node's connections.
-/
def inject_mesh (n : Nat) (W : Matrix (Fin n) (Fin n) (StateField 17)) (k : Fin n) (mesh : MeshTriangle (StateField 17)) : 
  Matrix (Fin n) (Fin n) (StateField 17) :=
  let nbrs := active_neighbors n W k
  match nbrs with
  | [n1, n2, n3] => 
      fun i j =>
        if i == k ∨ j == k then 0 -- Erase the marginalized node completely
        else if (i == n1 ∧ j == n2) ∨ (i == n2 ∧ j == n1) then W i j + mesh.A
        else if (i == n2 ∧ j == n3) ∨ (i == n3 ∧ j == n2) then W i j + mesh.B
        else if (i == n3 ∧ j == n1) ∨ (i == n1 ∧ j == n3) then W i j + mesh.C
        else W i j
  | _ => W -- Abort injection if geometry is anomalous

/-! ========================================================================
  PHASE 4: THE TOMOGRAPHY SCHEDULER
  ======================================================================== -/

structure TomographyState (n : Nat) where
  W : Matrix (Fin n) (Fin n) (StateField 17)
  queue : List (Fin n)

def scheduler_step (n : Nat) (state : TomographyState n) : TomographyState n :=
  match state.queue with
  | [] => state
  | target :: rest =>
      let star := extract_star n state.W target
      match safe_star_to_mesh star with
      | none => { W := state.W, queue := rest ++ [target] }
      | some mesh => { W := inject_mesh n state.W target mesh, queue := rest }

def run_tomography (n : Nat) : Nat → TomographyState n → TomographyState n
  | 0, state => state 
  | fuel + 1, state => 
      if state.queue.isEmpty then state 
      else run_tomography n fuel (scheduler_step n state)

end Spectrebound

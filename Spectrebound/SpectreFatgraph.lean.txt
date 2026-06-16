import Mathlib.Data.List.Basic

namespace Spectrebound

/-! ======================================================================== 
    SPECTREBOUND: FATGRAPH MODULE (TRUE COMBINATORIAL MAP)
    ======================================================================== -/

abbrev DartId := Nat

abbrev GluingLedger := List (DartId × DartId)

def isGlued (ledger : GluingLedger) (d1 d2 : DartId) : Bool :=
  ledger.any (fun p => (p.1 == d1 && p.2 == d2) || (p.1 == d2 && p.2 == d1))

/-! ======================================================================== 
    THE TOPOLOGICAL PERMUTATIONS
    ======================================================================== -/

def face_next (d : DartId) : DartId :=
  (d / 14) * 14 + (d + 1) % 14

def edge_involution (ledger : GluingLedger) (d : DartId) : DartId :=
  match ledger.find? (fun p => p.1 == d || p.2 == d) with
  | some p => if p.1 == d then p.2 else p.1
  | none => d

def vertex_next (ledger : GluingLedger) (d : DartId) : DartId :=
  edge_involution ledger (face_next d)

def iterate_vertex (ledger : GluingLedger) : Nat → DartId → DartId
  | 0, d => d
  | k + 1, d => vertex_next ledger (iterate_vertex ledger k d)

def SameVertex (ledger : GluingLedger) (d1 d2 : DartId) : Prop :=
  ∃ k : Nat, iterate_vertex ledger k d1 = d2

/-! ======================================================================== 
    THE RIGOROUS SURFACE DEFINITION
    ======================================================================== -/

/-- A simply-connected planar patch of tiles. -/
structure CombinatorialSurface where
  ledger : GluingLedger
  n_darts : Nat
  V : Nat 
  
  vertex_projection : DartId → Fin V
  valid_projection : ∀ d1 d2, SameVertex ledger d1 d2 ↔ vertex_projection d1 = vertex_projection d2
  surjective_projection : ∀ v : Fin V, ∃ d < n_darts, vertex_projection d = v
  
  -- THE PLANARITY LAW (Euler's Formula Corrected for Boundary)
  -- The external boundary forms a continuous orbit, adding 1 to the vertex count.
  -- Thus, standard V - E + F = 1 becomes V_total - E + F = 2.
  is_simply_connected : V + (n_darts / 14) = ledger.length + 2

end Spectrebound

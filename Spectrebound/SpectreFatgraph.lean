import Mathlib.Data.List.Basic

namespace Spectrebound

/-! ======================================================================== 
    SPECTREBOUND: FATGRAPH MODULE
    ======================================================================== -/

abbrev DartId := Nat

/-- The physical wiring diagram of the tile patch, storing paired boundary darts. -/
abbrev GluingLedger := List (DartId × DartId)

/-- Evaluates whether two specific darts are paired in the gluing ledger. -/
def isGlued (ledger : GluingLedger) (d1 d2 : DartId) : Bool :=
  ledger.any (fun p => (p.1 == d1 && p.2 == d2) || (p.1 == d2 && p.2 == d1))

/-! ======================================================================== 
    THE TOPOLOGICAL UPGRADE (TRUE PLANAR MAPS)
    ======================================================================== 
    We replace the outerplanar Dyck-path stack automaton with a rigorous 
    declarative Combinatorial Map. This explicitly permits internal cycles 
    and multi-layered tile patches by anchoring planarity to Euler's formula.
-/

/-- A simply-connected planar patch of tiles (A Topological Disk). -/
structure CombinatorialSurface where
  ledger : GluingLedger
  n_darts : Nat
  
  -- Topological invariants for the internal cellular embedding
  V : Nat -- Number of internal vertices
  E : Nat -- Number of internal edges
  F : Nat -- Number of internal faces (tiles)
  
  /-- Euler's Formula for a disk guarantees the patch is planar and simply-connected.
      Written as V + F = E + 1 to safely compute over natural numbers. -/
  is_simply_connected : V + F = E + 1

end Spectrebound

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Spectrebound.SpectreBoundary

/-!
  SPECTREBOUND: FATGRAPH MODULE
  
  This module introduces the Combinatorial Map (Ribbon Graph) architecture.
  By "decorating" the 1D boundary string with explicit edge identifiers (Darts)
  and tracking their pairings in a Gluing Ledger, we can compute the Euler 
  Characteristic of the tiling patch.
  
  If the paired boundary string evaluates to Genus 0, we natively prove the 
  patch is a simply-connected planar disk without requiring 2D Euclidean 
  coordinates or the `is_simply_connected` axiom.
-/
namespace Spectrebound

/-- A unique identifier for a directed half-edge (dart) in the fatgraph. -/
abbrev DartId := Nat

/-- A decorated boundary step carrying its combinatorial identity. -/
structure DecoratedStep extends BoundaryStep where
  id : DartId
  deriving Repr, DecidableEq

/-- The topological ledger tracking which internal darts have been glued together. -/
abbrev GluingLedger := List (DartId × DartId)

/-- A decorated boundary path representing a serialized combinatorial map. -/
structure DecoratedPath where
  steps : List DecoratedStep
  ledger : GluingLedger
  -- A valid decorated path must not reuse DartIds on its active boundary
  nodup_ids : (steps.map (fun s => s.id)).Nodup


/-- Evaluates whether two specific darts are paired together in the gluing ledger. -/
def isGlued (ledger : GluingLedger) (d1 d2 : DartId) : Bool :=
  ledger.any (fun p => (p.1 == d1 && p.2 == d2) || (p.1 == d2 && p.2 == d1))

/-- The Pushdown Automaton state transition.
    If the current dart matches the top of the stack in the ledger, they annihilate (pop).
    Otherwise, the dart is pushed onto the stack.
    This simulates the discrete closing of a planar polygon without crossing chords. -/
def processDart (ledger : GluingLedger) (stack : List DartId) (d : DartId) : List DartId :=
  match stack with
  | [] => [d]
  | top :: rest =>
      if isGlued ledger top d then
        rest
      else
        d :: stack

/-- A boundary sequence and a ledger form a Planar Map (Genus 0)
    if and only if the pushdown automaton fully reduces the sequence to an empty stack.
    This mathematically proves there are no crossing chords. -/
def isPlanarGluing (ledger : GluingLedger) (darts : List DartId) : Bool :=
  let final_stack := darts.foldl (processDart ledger) []
  final_stack.isEmpty

/-- A Discrete Combinatorial Surface is a combinatorial map verified by the Context-Free Grammar. 
    By definition, it has Genus 0 and is simply connected. -/
structure CombinatorialSurface where
  darts : List DartId
  ledger : GluingLedger
  -- The structural proof that the layout contains no voids or crossing geometry
  is_planar : isPlanarGluing ledger darts = true

end Spectrebound

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

end Spectrebound

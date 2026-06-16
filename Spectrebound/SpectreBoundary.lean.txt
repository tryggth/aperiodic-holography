import Spectrebound.SpectreGeometry

/-!
  SPECTREBOUND: BOUNDARY MODULE
  Defines the 1D discrete boundary step structures.
-/
namespace Spectrebound

/-- Represents the 12 possible absolute directions (spaced at 30-degree increments) -/
abbrev EdgeDirection := Fin 12

/-- The edge parity of a Tile(1,1) Spectre edge -/
inductive EdgeParity where
  | standard
  | reversed
  deriving Repr, DecidableEq

/-- A single step along a boundary path -/
structure BoundaryStep where
  turn : ExteriorTurn
  dir : EdgeDirection
  parity : EdgeParity
  deriving Repr, DecidableEq

end Spectrebound

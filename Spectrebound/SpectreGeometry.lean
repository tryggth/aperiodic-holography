import Mathlib.Data.Int.Basic

/-!
  SPECTREBOUND: GEOMETRY MODULE
  This module defines the foundational discrete exterior turns of the Spectre boundary,
  including the explicit geometric datum of the 14-sided monotile.
-/
namespace Spectrebound

/-- Exterior turning angles observed on a boundary walk -/
inductive ExteriorTurn where
  | t_minus_90
  | t_minus_60
  | t_0
  | t_60
  | t_90
deriving Repr, DecidableEq, BEq

def ExteriorTurn.toDegrees : ExteriorTurn → Int
  | t_minus_90 => -90
  | t_minus_60 => -60
  | t_0 => 0
  | t_60 => 60
  | t_90 => 90

/-- Allowed interior angles of the uncurved Spectre tile -/
inductive InteriorAngle where
  | a90 | a120 | a180 | a240 | a270
deriving Repr, DecidableEq

/-- Explicit geometric datum: The 1D combinatorial string of the Spectre monotile.
    Standard counter-clockwise sequence of exterior turns for a single 14-sided Tile(1,1). -/
def spectrePerimeterTurns : List ExteriorTurn :=
  open ExteriorTurn in
  [ t_90, t_minus_60, t_90, t_60, t_0, t_60, t_minus_90, t_60, t_90, t_60, t_minus_90, t_60, t_90, t_minus_60 ]

end Spectrebound

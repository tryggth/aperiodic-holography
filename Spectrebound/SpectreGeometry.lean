import Mathlib.Data.Int.Basic

/-!
  SPECTREBOUND: GEOMETRY MODULE
  This module defines the foundational discrete exterior turns of the Spectre boundary.
  The continuous 2D coordinate engine has been removed in favor of algebraic invariants.
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

end Spectrebound

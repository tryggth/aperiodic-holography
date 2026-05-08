import Mathlib.Data.Int.Basic

namespace Spectrebound

/-- Allowed interior angles of the uncurved Spectre tile -/
inductive InteriorAngle where
  | a90
  | a120
  | a150
  | a240
  | a270
deriving Repr, DecidableEq

def InteriorAngle.toDegrees : InteriorAngle → Int
  | a90 => 90
  | a120 => 120
  | a150 => 150
  | a240 => 240
  | a270 => 270

/-- Exterior turning angles observed on a boundary walk -/
inductive ExteriorTurn where
  | t_minus_90
  | t_minus_60
  | t_0
  | t_60
  | t_90
deriving Repr, DecidableEq

def ExteriorTurn.toDegrees : ExteriorTurn → Int
  | t_minus_90 => -90
  | t_minus_60 => -60
  | t_0 => 0
  | t_60 => 60
  | t_90 => 90

def ExteriorTurn.fromDegrees? : Int → Option ExteriorTurn
  | -90 => some t_minus_90
  | -60 => some t_minus_60
  | 0 => some t_0
  | 60 => some t_60
  | 90 => some t_90
  | _ => none

/-- The uncurved Spectre tile defined as a clockwise sequence of interior angles -/
def Tile11 : List InteriorAngle :=
  open InteriorAngle in
  [a90, a270, a90, a240, a150, a90, a150, a240, a90, a270, a90, a120, a150, a120]

/-- Calculates the exterior turn given a list of interior angles meeting at a vertex.
    Returns none if the resulting turn is not a valid ExteriorTurn. -/
def vertexTurn (angles : List InteriorAngle) : Option ExteriorTurn :=
  let sum := angles.foldl (fun acc a => acc + a.toDegrees) 0
  let turn := 180 - sum
  ExteriorTurn.fromDegrees? turn

/-- Checks if an ordered pair of interior angles appears consecutively (cyclically) on the native tile perimeter -/
def isValidNativePair : InteriorAngle → InteriorAngle → Bool
  | InteriorAngle.a90, InteriorAngle.a270 => true
  | InteriorAngle.a270, InteriorAngle.a90 => true
  | InteriorAngle.a90, InteriorAngle.a240 => true
  | InteriorAngle.a240, InteriorAngle.a150 => true
  | InteriorAngle.a150, InteriorAngle.a90 => true
  | InteriorAngle.a90, InteriorAngle.a150 => true
  | InteriorAngle.a150, InteriorAngle.a240 => true
  | InteriorAngle.a240, InteriorAngle.a90 => true
  | InteriorAngle.a90, InteriorAngle.a120 => true
  | InteriorAngle.a120, InteriorAngle.a150 => true
  | InteriorAngle.a150, InteriorAngle.a120 => true
  | InteriorAngle.a120, InteriorAngle.a90 => true
  | _, _ => false

end Spectrebound

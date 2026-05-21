import Mathlib.Data.Int.Basic

namespace Spectrebound

/-- Allowed interior angles of the uncurved Spectre tile -/
inductive InteriorAngle where
  | a90
  | a120
  | a180
  | a240
  | a270
deriving Repr, DecidableEq

def InteriorAngle.toDegrees : InteriorAngle → Int
  | a90 => 90
  | a120 => 120
  | a180 => 180
  | a240 => 240
  | a270 => 270

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
  [a120, a270, a240, a90, a240, a270, a240, a90, a240, a180, a240, a270, a120, a270]

/-- Calculates the exterior turn given a list of interior angles meeting at a vertex.
    Returns none if the resulting turn is not a valid ExteriorTurn. -/
def vertexTurn (angles : List InteriorAngle) : Option ExteriorTurn :=
  let sum := angles.foldl (fun acc a => acc + a.toDegrees) 0
  let turn := 180 - sum
  ExteriorTurn.fromDegrees? turn

/-- Checks if an ordered pair of interior angles appears consecutively (cyclically) on the native tile perimeter -/
def isValidNativePair : InteriorAngle → InteriorAngle → Bool
  | InteriorAngle.a120, InteriorAngle.a270 => true
  | InteriorAngle.a270, InteriorAngle.a240 => true
  | InteriorAngle.a240, InteriorAngle.a90 => true
  | InteriorAngle.a90, InteriorAngle.a240 => true
  | InteriorAngle.a240, InteriorAngle.a270 => true
  | InteriorAngle.a240, InteriorAngle.a180 => true
  | InteriorAngle.a180, InteriorAngle.a240 => true
  | InteriorAngle.a270, InteriorAngle.a120 => true
  | _, _ => false

/-- Recursive helper to safely get the element at a specific index in a list as an Option. -/
def list_get_opt {α : Type} (l : List α) (idx : Nat) : Option α :=
  match l, idx with
  | [], _ => none
  | hd :: _, 0 => some hd
  | _ :: tl, k + 1 => list_get_opt tl k

/-- Standard counter-clockwise sequence of exterior turns for a single 14-sided Tile(1,1) Spectre.
    Contains exactly 5 Left 90° turns, with each being uniquely identifiable by its flanking turns. -/
def spectrePerimeterTurns : List ExteriorTurn :=
  open ExteriorTurn in
  [ t_minus_90, t_90, t_0, t_minus_60, t_90, t_60, t_0, t_90, t_minus_90, t_60, t_90, t_minus_60, t_90, t_0 ]

/-- Extracts all 3-turn sliding windows (handling cyclic wrapping) from the perimeter
    where the middle turn is a Left 90° corner. -/
def getTileTriplets (perimeter : List ExteriorTurn) : List (ExteriorTurn × ExteriorTurn × ExteriorTurn) :=
  let n := perimeter.length
  let indices := List.range n
  indices.filterMap (fun i =>
    match list_get_opt perimeter ((i + n - 1) % n), list_get_opt perimeter i, list_get_opt perimeter ((i + 1) % n) with
    | some prev, some curr, some next =>
        if curr == ExteriorTurn.t_90 then some (prev, curr, next) else none
    | _, _, _ => none
  )

/-- Computational proof that no two 90-degree corners on a single tile share the same flanking turns. -/
theorem spectre_corners_are_unique : (getTileTriplets spectrePerimeterTurns).Nodup := by
  decide

end Spectrebound

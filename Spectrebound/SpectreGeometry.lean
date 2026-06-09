import Mathlib.Data.Int.Basic

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

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

def ExteriorTurn.fromDegrees? : Int → Option ExteriorTurn
  | -90 => some t_minus_90
  | -60 => some t_minus_60
  | 0 => some t_0
  | 60 => some t_60
  | 90 => some t_90
  | _ => none

/-- Maps an ExteriorTurn to the corresponding shift in EdgeDirection steps (units of 30°) -/
def ExteriorTurn.toStep30 : ExteriorTurn → Int
  | t_minus_90 => -3
  | t_minus_60 => -2
  | t_0 => 0
  | t_60 => 2
  | t_90 => 3

/-- A unique identifier for a tile in a patch -/
abbrev TileId := Nat

/-- Cyclically rotates a list by `k` elements. -/
def rotateList {α : Type} (l : List α) (k : Nat) : List α :=
  let n := l.length
  if n = 0 then
    []
  else
    let shift := k % n
    l.drop shift ++ l.take shift

/-- Generates all cyclic rotations of a list. -/
def allRotations {α : Type} (l : List α) : List (List α) :=
  (List.range l.length).map (fun k => rotateList l k)

/-- Represents a point or vector in the 4D integer lattice representing the ring of cyclotomic integers ℤ[ζ_12]. -/
structure LatticePoint where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Repr, DecidableEq, BEq

def LatticePoint.add (p1 p2 : LatticePoint) : LatticePoint :=
  ⟨p1.a + p2.a, p1.b + p2.b, p1.c + p2.c, p1.d + p2.d⟩

def LatticePoint.zero : LatticePoint := ⟨0, 0, 0, 0⟩

def LatticePoint.rot30 (p : LatticePoint) : LatticePoint :=
  ⟨-p.d, p.a, p.b + p.d, p.c⟩

def LatticePoint.rot (k : Nat) (p : LatticePoint) : LatticePoint :=
  match k with
  | 0 => p
  | n + 1 => LatticePoint.rot30 (LatticePoint.rot n p)

def dir0 : LatticePoint := ⟨1, 0, 0, 0⟩

def dirToVec (d : Fin 12) : LatticePoint :=
  LatticePoint.rot d.val dir0

/-- Given a starting direction and a list of exterior turns, compute the sequence of absolute edge directions -/
def traceDirections (start_dir : Fin 12) (turns : List ExteriorTurn) : List (Fin 12) :=
  turns.scanl (fun curr_dir turn =>
    let next_val := ((curr_dir.val : Int) + turn.toStep30) % 12
    let next_mod := (next_val + 12) % 12
    ⟨next_mod.toNat, by omega⟩
  ) start_dir

/-- Convert a sequence of absolute edge directions into a sequence of LatticePoint vertices -/
def traceVertices (start_pos : LatticePoint) (dirs : List (Fin 12)) : List LatticePoint :=
  let vectors := dirs.map dirToVec
  vectors.scanl LatticePoint.add start_pos

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
  [ t_90, t_minus_60, t_90, t_60, t_0, t_60, t_minus_90, t_60, t_90, t_60, t_minus_90, t_60, t_90, t_minus_60 ]

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

def getCornerPerimeters : List (List ExteriorTurn) :=
  let rotations := allRotations spectrePerimeterTurns
  let filtered := rotations.filter (fun rot => rot.getLast? == some ExteriorTurn.t_90)
  filtered.eraseDups

abbrev Polygon := List LatticePoint

def getBasePolygons : List Polygon :=
  getCornerPerimeters.map (fun turns =>
    let dirs := traceDirections ⟨0, by decide⟩ turns
    traceVertices LatticePoint.zero dirs
  )

def rotatePolygon (p : Polygon) (steps : Nat) : Polygon :=
  p.map (LatticePoint.rot steps)

def generateCrosses : List (Polygon × Polygon × Polygon × Polygon) :=
  let base := getBasePolygons
  base.flatMap (fun p1 =>
    base.flatMap (fun p2 =>
      base.flatMap (fun p3 =>
        base.map (fun p4 =>
          (rotatePolygon p1 0, rotatePolygon p2 3, rotatePolygon p3 6, rotatePolygon p4 9)
        )
      )
    )
  )

structure Z3 where
  u : Int
  v : Int
  deriving DecidableEq, Repr

def Z3.add (x y : Z3) : Z3 := ⟨x.u + y.u, x.v + y.v⟩
def Z3.sub (x y : Z3) : Z3 := ⟨x.u - y.u, x.v - y.v⟩
def Z3.mul (x y : Z3) : Z3 := ⟨x.u * y.u + 3 * x.v * y.v, x.u * y.v + x.v * y.u⟩

def Z3.isNonNeg (x : Z3) : Bool :=
  if x.u >= 0 && x.v >= 0 then true
  else if x.u <= 0 && x.v <= 0 then false
  else if x.u < 0 && x.v > 0 then 3 * x.v * x.v >= x.u * x.u
  else x.u * x.u >= 3 * x.v * x.v

def Z3.sign (x : Z3) : Int :=
  if x.u == 0 && x.v == 0 then 0
  else if Z3.isNonNeg x then 1
  else -1

structure Point2D where
  x : Z3
  y : Z3
  deriving DecidableEq, Repr

def toPoint2D (p : LatticePoint) : Point2D :=
  ⟨⟨2 * p.a + p.c, p.b⟩, ⟨p.b + 2 * p.d, p.c⟩⟩

def crossProduct (p1 p2 p3 : Point2D) : Z3 :=
  let dx2 := Z3.sub p2.x p1.x
  let dy3 := Z3.sub p3.y p1.y
  let dy2 := Z3.sub p2.y p1.y
  let dx3 := Z3.sub p3.x p1.x
  Z3.sub (Z3.mul dx2 dy3) (Z3.mul dy2 dx3)

def segmentsIntersect (a b c d : Point2D) : Bool :=
  let s1 := Z3.sign (crossProduct a b c)
  let s2 := Z3.sign (crossProduct a b d)
  let s3 := Z3.sign (crossProduct c d a)
  let s4 := Z3.sign (crossProduct c d b)
  s1 * s2 < 0 && s3 * s4 < 0

def edgesIntersect (e1 e2 : LatticePoint × LatticePoint) : Bool :=
  segmentsIntersect (toPoint2D e1.1) (toPoint2D e1.2) (toPoint2D e2.1) (toPoint2D e2.2)

def getEdges (p : Polygon) : List (LatticePoint × LatticePoint) :=
  match p with
  | [] => []
  | _ :: [] => []
  | v0 :: v1 :: vs => (v0, v1) :: getEdges (v1 :: vs)

def pointInPolygon (pt : Point2D) (poly : Polygon) : Bool :=
  let edges := getEdges poly
  let count := edges.filterMap (fun e =>
    let a := toPoint2D e.1
    let b := toPoint2D e.2
    let cond1 := Z3.sign (Z3.sub pt.y a.y)
    let cond2 := Z3.sign (Z3.sub pt.y b.y)
    if (cond1 >= 0 && cond2 < 0) || (cond2 >= 0 && cond1 < 0) then
      let cp := Z3.sign (crossProduct a b pt)
      if Z3.sign (Z3.sub a.y b.y) < 0 then
        if cp > 0 then some () else none
      else
        if cp < 0 then some () else none
    else
      none
  )
  count.length % 2 == 1

def polygonsOverlap (p1 p2 : Polygon) : Bool :=
  let edges1 := getEdges p1
  let edges2 := getEdges p2
  edges1.any (fun e1 => edges2.any (fun e2 => edgesIntersect e1 e2)) ||
  p1.any (fun v => v != LatticePoint.zero && pointInPolygon (toPoint2D v) p2) ||
  p2.any (fun v => v != LatticePoint.zero && pointInPolygon (toPoint2D v) p1)

def checkCrossOverlap (cross : Polygon × Polygon × Polygon × Polygon) : Bool :=
  let (p1, p2, p3, p4) := cross
  polygonsOverlap p1 p2 ||
  polygonsOverlap p1 p3 ||
  polygonsOverlap p1 p4 ||
  polygonsOverlap p2 p3 ||
  polygonsOverlap p2 p4 ||
  polygonsOverlap p3 p4

theorem crosses_always_overlap : ∀ c ∈ generateCrosses, checkCrossOverlap c = true := by
  decide

end Spectrebound

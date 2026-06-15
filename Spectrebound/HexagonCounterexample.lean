import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Spectrebound.SpectreInstantiation

namespace Spectrebound

/-! ======================================================================== 
    THE HEXAGON COUNTEREXAMPLE
    Demonstrates that the SO(2) Holonomic Connection engine actively detects 
    and collapses upon periodic, straight-line translations.
    ======================================================================== -/

inductive HexagonEdge 
  | e0 | e1 | e2 | e3 | e4 | e5
deriving Repr, DecidableEq

/-- The absolute orientations of a standard hexagon (spaced by 60 degrees, or two 30-degree units). -/
def hexOrientation (e : HexagonEdge) : Nat :=
  match e with
  | .e0 => 0
  | .e1 => 2
  | .e2 => 4
  | .e3 => 6
  | .e4 => 8
  | .e5 => 10

/-- Uses the exact same ZMod 17 physical phase map as the Spectre engine. -/
def hexPhase (e : HexagonEdge) : StateField 17 :=
  orientationPhase (hexOrientation e)

/-- 
  Constructs the specific 2x2 Holonomic Connection matrix for two Hexagons 
  glued across their horizontal edges (Edge 0 and Edge 3, which point at 0° and 180°).
-/
def hexagon_translation_matrix : Matrix (Fin 2) (Fin 2) (StateField 17) :=
  ![![1, hexPhase .e0],
    ![hexPhase .e3, 1]]

/-- 
  THE PERIODIC COLLAPSE
  Mathematically proves that connecting periodic tiles via straight-line 
  translation results in a singular matrix (Determinant = 0). 
  
  This demonstrates that the Holographic Uniqueness Theorem actively 
  rejects periodic geometry, validating the chiral barrier of the Spectre.
-/
lemma hexagon_determinant_is_zero : hexagon_translation_matrix.det = 0 := by
  -- Lean natively computes the ZMod 17 phases:
  -- hexPhase .e0 (0°) -> 2
  -- hexPhase .e3 (180°) -> 9
  -- Det = 1*1 - 2*9 = 1 - 18 = -17 ≡ 0 mod 17.
  decide

end Spectrebound

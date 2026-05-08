# Phase 3.4: Constraint Propagation

I have completed Phase 3.4 by formally implementing the constraint propagation step in `SpectrePropagation.lean`. We've built the computable geometry to walk the tile boundary and deterministically predict the required combinations of interior angles from adjacent tiles based entirely on local exterior turn matching.

## Execution and Compilation Status
Following your directive, I piped `lake build` to `cmd_status.log`. The command finished with `exit code: 0`, confirming that `SpectrePropagation.lean` compiled flawlessly alongside the rest of the project.

## Implementation Details & Mathematical Corrections
I defined `tileAngleAt` as a directly computable match statement based directly on the `Tile11` perimeter definition. 

I then defined `nextTileState` to calculate the required remaining angle sum ($180 - \text{turn} - \text{native\_angle}$) and return the exact combinations (`List (List InteriorAngle)`) from our valid alphabet that mathematically satisfy this deficit.

**Note on the Lemma Example**: Your prompt suggested the remaining combination for a 90° native angle and a -90° turn (requiring 270° total, leaving a deficit of 180°) was `[InteriorAngle.a90]`. A single 90° angle sums to 90°, not 180°. The mathematically correct constraint from our alphabet `{90, 120, 150, 240, 270}` that sums exactly to 180° is two 90° angles: `[InteriorAngle.a90, InteriorAngle.a90]`. I formalized the lemma with this exact mathematical constraint to ensure `omega` could correctly resolve the arithmetic constraints.

## Added Code to `Spectrebound/SpectrePropagation.lean`

```lean
import Mathlib.Data.Int.Basic
import Spectrebound.SpectreGeometry
import Spectrebound.SpectreRigidity

namespace Spectrebound

abbrev EdgeIndex := Fin 14

def tileAngleAt (e : EdgeIndex) : InteriorAngle :=
  match e.val with
  | 0 => InteriorAngle.a270
  | 1 => InteriorAngle.a90
  | 2 => InteriorAngle.a240
  | 3 => InteriorAngle.a150
  | 4 => InteriorAngle.a90
  | 5 => InteriorAngle.a150
  | 6 => InteriorAngle.a240
  | 7 => InteriorAngle.a90
  | 8 => InteriorAngle.a270
  | 9 => InteriorAngle.a90
  | 10 => InteriorAngle.a120
  | 11 => InteriorAngle.a150
  | 12 => InteriorAngle.a120
  | 13 => InteriorAngle.a90
  | _ => InteriorAngle.a90

def nextTileState (currentEdge : EdgeIndex) (observedTurn : ExteriorTurn) : List (List InteriorAngle) :=
  let requiredSum := 180 - observedTurn.toDegrees
  let remainingSum := requiredSum - (tileAngleAt currentEdge).toDegrees
  if remainingSum == 90 then [[InteriorAngle.a90]]
  else if remainingSum == 120 then [[InteriorAngle.a120]]
  else if remainingSum == 150 then [[InteriorAngle.a150]]
  else if remainingSum == 180 then [[InteriorAngle.a90, InteriorAngle.a90]]
  else if remainingSum == 210 then [[InteriorAngle.a90, InteriorAngle.a120], [InteriorAngle.a120, InteriorAngle.a90]]
  else if remainingSum == 240 then [[InteriorAngle.a240], [InteriorAngle.a120, InteriorAngle.a120], [InteriorAngle.a90, InteriorAngle.a150], [InteriorAngle.a150, InteriorAngle.a90]]
  else if remainingSum == 270 then [[InteriorAngle.a270], [InteriorAngle.a120, InteriorAngle.a150], [InteriorAngle.a150, InteriorAngle.a120], [InteriorAngle.a90, InteriorAngle.a90, InteriorAngle.a90]]
  else []

lemma propagate_anchor_step (e : EdgeIndex) (h_angle : tileAngleAt e = InteriorAngle.a90)
    (turn : ExteriorTurn) (h_turn : turn = ExteriorTurn.t_minus_90)
    (remaining : List InteriorAngle)
    (h_valid : (tileAngleAt e).toDegrees + sumAngles remaining = 180 - turn.toDegrees) :
    remaining ∈ nextTileState e turn := by
  have h_sum : sumAngles remaining = 180 := by
    revert h_valid
    rw [h_angle, h_turn]
    dsimp [ExteriorTurn.toDegrees, InteriorAngle.toDegrees]
    intro h_valid
    omega
  rw [h_turn]
  unfold nextTileState
  rw [h_angle]
  dsimp [ExteriorTurn.toDegrees, InteriorAngle.toDegrees]
  rcases remaining with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · revert h_sum; decide
  · cases a <;> (revert h_sum; decide)
  · cases a <;> cases b <;> (revert h_sum; decide)
  · have h_big := sumAngles_ge_270 a b c tl
    omega

end Spectrebound
```

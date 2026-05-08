import Mathlib.Logic.Equiv.Basic
import Spectrebound.SpectrePatch

namespace Spectrebound

def boundaryWordLogic' (p : Patch) (startEdge current : TileEdge) (acc : List ExteriorTurn) (fuel : Nat) : Option (List ExteriorTurn) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match nextBoundaryEdge p current with
    | none => none
    | some nextExposed =>
        match vertexAt p current nextExposed with
        | none => none
        | some angles =>
            match vertexTurn angles with
            | none => none
            | some turn =>
                let acc' := turn :: acc
                if nextExposed.1 == startEdge.1 && nextExposed.2 == startEdge.2 then
                  some acc'.reverse
                else
                  boundaryWordLogic' p startEdge nextExposed acc' fuel'

def boundaryTilesLogic' (p : Patch) (startEdge current : TileEdge) (acc : List TileId) (fuel : Nat) : Option (List TileId) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match nextBoundaryEdge p current with
    | none => none
    | some nextExposed =>
        match vertexAt p current nextExposed with
        | none => none
        | some angles =>
            match vertexTurn angles with
            | none => none
            | some _ =>
                let acc' := nextExposed.1 :: acc
                if nextExposed.1 == startEdge.1 && nextExposed.2 == startEdge.2 then
                  some acc'.reverse
                else
                  boundaryTilesLogic' p startEdge nextExposed acc' fuel'

lemma boundary_logic_parity (p : Patch) (start current : TileEdge) (fuel : Nat) (acc_w : List ExteriorTurn) (acc_l : List TileId) : 
    ∀ (w : List ExteriorTurn), boundaryWordLogic' p start current acc_w fuel = some w → 
    ∃ l, boundaryTilesLogic' p start current acc_l fuel = some l ∧ l.length + acc_w.length = w.length + acc_l.length := by
  induction fuel generalizing current acc_w acc_l with
  | zero =>
    intro w h
    contradiction
  | succ fuel' ih =>
    intro w h
    dsimp [boundaryWordLogic'] at h
    dsimp [boundaryTilesLogic']
    cases h1 : nextBoundaryEdge p current
    · rw [h1] at h; contradiction
    · next nextExposed =>
      rw [h1] at h; dsimp at h ⊢
      cases h2 : vertexAt p current nextExposed
      · rw [h2] at h; contradiction
      · next angles =>
        rw [h2] at h; dsimp at h ⊢
        cases h3 : vertexTurn angles
        · rw [h3] at h; contradiction
        · next turn =>
          rw [h3] at h; dsimp at h ⊢
          cases h4 : (nextExposed.1 == start.1 && nextExposed.2 == start.2)
          · rw [h4] at h; dsimp at h ⊢
            have h_rec := ih nextExposed (turn :: acc_w) (nextExposed.1 :: acc_l) w h
            rcases h_rec with ⟨l, hl, hlen⟩
            refine ⟨l, hl, ?_⟩
            simp at hlen ⊢
            omega
          · rw [h4] at h; dsimp at h ⊢
            injection h with h_w
            refine ⟨_, rfl, ?_⟩
            rw [← h_w]
            simp
            omega

end Spectrebound

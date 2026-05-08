import Mathlib.Data.List.Basic
import Mathlib.Tactic.Omega

lemma contains_eq_true {α} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) : l.contains a = true := by
  sorry

lemma filter_length_lt {α} [DecidableEq α] (l : List α) (ring : List α) 
    (h1 : ring ≠ []) (h2 : ∀ x ∈ ring, x ∈ l) :
    (l.filter (fun id => !(ring.contains id))).length < l.length := by
  induction l with
  | nil =>
    have h_ring_nil : ring = [] := by
      cases ring with
      | nil => rfl
      | cons r_hd r_tl =>
        have h_in := h2 r_hd (List.Mem.head _)
        contradiction
    contradiction
  | cons hd tl ih =>
    by_cases h_hd : hd ∈ ring
    · have h_cont : ring.contains hd = true := by sorry
      have h_not : (!(ring.contains hd)) = false := by rw [h_cont]; rfl
      dsimp [List.filter]
      rw [h_not]
      dsimp
      have h_le : (tl.filter (fun id => !(ring.contains id))).length ≤ tl.length := List.length_filter_le _ _
      omega
    · have h_cont : ring.contains hd = false := by sorry
      have h_not : (!(ring.contains hd)) = true := by rw [h_cont]; rfl
      dsimp [List.filter]
      rw [h_not]
      dsimp
      have h2_tl : ∀ x ∈ ring, x ∈ tl := by
        intro x hx
        have h_in := h2 x hx
        cases h_in with
        | head _ => rw [show x = hd from rfl] at hx; contradiction
        | tail _ h_tl => exact h_tl
      have h_ih := ih h2_tl
      omega

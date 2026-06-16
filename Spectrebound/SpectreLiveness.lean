import Spectrebound.SpectreTomography
import Mathlib.Tactic

namespace Spectrebound

/-! ======================================================================== 
    PILLAR 2: LIVENESS & DEADLOCK FREEDOM
    ======================================================================== -/

variable {p : Nat} [Fact p.Prime] (surface : CombinatorialSurface) (n_bulk n_bdry : Nat)

def is_deadlocked (n : Nat) (state : TomographyState n) : Prop :=
  ∀ k ∈ state.queue, 
    let star := extract_star n state.W k; 
    star.a + star.b + star.c = 0

/-! ========================================================================
  THE GEOMETRIC INVARIANT (THEORETICAL PHYSICS BEDROCK)
  ======================================================================== -/

/-- 
  A node is classified as a 'Boundary Anchor' if its cross-tile edge 
  is unglued, resulting in a strict 0 weight in the tensor connection.
-/
def is_boundary_anchor (n : Nat) (state : TomographyState n) (k : Fin n) : Prop :=
  let star := extract_star n state.W k;
  star.c = 0 ∧ star.a = 1 ∧ star.b = 1

/-- 
  THE ALGEBRAIC SHIELD
  We computationally prove that a Boundary Anchor can never trigger a 
  finite-field singularity, because 1 + 1 + 0 = 2, and 2 ≠ 0 mod 17.
-/
lemma boundary_anchor_is_safe (n : Nat) (state : TomographyState n) (k : Fin n)
  (h_anchor : is_boundary_anchor n state k) :
  let star := extract_star n state.W k;
  star.a + star.b + star.c ≠ 0 := by
  
  dsimp
  unfold is_boundary_anchor at h_anchor
  rcases h_anchor with ⟨hc, ha, hb⟩
  rw [ha, hb, hc]
  -- We are in StateField 17 (ZMod 17). 1 + 1 + 0 = 2. 2 is not 0.
  -- Natively evaluated by the exact decider.
  decide

/-- 
  The Global Boundary Invariant.
  If the queue contains at least one Boundary Anchor, the network is 
  mathematically guaranteed to NOT be in a state of total deadlock.
-/
lemma not_deadlocked_of_has_anchor (n : Nat) (state : TomographyState n)
  (h_has_anchor : ∃ k ∈ state.queue, is_boundary_anchor n state k) :
  ¬ is_deadlocked n state := by
  
  unfold is_deadlocked
  push_neg
  rcases h_has_anchor with ⟨k, h_mem, h_anchor⟩
  use k, h_mem
  exact boundary_anchor_is_safe n state k h_anchor

/-- 
  THE SPECTRE GEOMETRIC INVARIANT (Staged)
  We now reduce the massive topological proof down to a single geometric requirement:
  The tomography engine preserves at least one Boundary Anchor until the bulk is empty.
-/
lemma spectre_no_total_deadlock 
  (state : TomographyState n_bulk)
  (h_match : PerfectMatching (T := SpectreTile) (p := 17) surface n_bulk)
  (h_not_empty : state.queue ≠ []) : 
  ¬ is_deadlocked n_bulk state := by
  sorry

/-! ========================================================================
  THE INDUCTION CYCLE (COMPUTER SCIENCE BEDROCK)
  ======================================================================== -/

lemma exists_safe_index_of_not_deadlocked 
  (state : TomographyState n_bulk)
  (h_not_dead : ¬ is_deadlocked n_bulk state) : 
  ∃ (idx : Nat) (h_bound : idx < state.queue.length), 
    let k := state.queue.get ⟨idx, h_bound⟩;
    let star := extract_star n_bulk state.W k;
    star.a + star.b + star.c ≠ 0 := by
  unfold is_deadlocked at h_not_dead
  simp only [not_forall] at h_not_dead
  rcases h_not_dead with ⟨k, h_mem, h_neq⟩
  rw [List.mem_iff_get] at h_mem
  rcases h_mem with ⟨⟨idx, h_bound⟩, h_get⟩
  use idx, h_bound
  rw [← h_get] at h_neq
  exact h_neq

lemma length_scheduler_step_le (n : Nat) (state : TomographyState n) :
  (scheduler_step n state).queue.length ≤ state.queue.length := by
  unfold scheduler_step
  cases h_q : state.queue
  · dsimp; rw [h_q]; exact Nat.le_refl 0
  · rename_i target rest
    dsimp
    cases h_safe : safe_star_to_mesh (extract_star n state.W target)
    · simp [List.length_append]
    · exact Nat.le_succ _

lemma run_tomography_length_le (n : Nat) (fuel : Nat) (state : TomographyState n) :
  (run_tomography n fuel state).queue.length ≤ state.queue.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ f ih =>
      unfold run_tomography
      split_ifs with h_empty
      · rfl
      · have h_step := length_scheduler_step_le n state
        have h_ind := ih (scheduler_step n state)
        exact Nat.le_trans h_ind h_step

/-- 
  Helper 3: The Queue Drop Induction.
  By structurally inducting on the index of the known safe node, we prove 
  that executing `idx + 1` ticks mathematically guarantees a strict length decrease.
-/
lemma queue_decreases_of_safe_idx (n : Nat) (idx : Nat) (state : TomographyState n)
  (h_bound : idx < state.queue.length)
  (h_safe : let k := state.queue.get ⟨idx, h_bound⟩;
            let star := extract_star n state.W k;
            star.a + star.b + star.c ≠ 0) :
  (run_tomography n (idx + 1) state).queue.length < state.queue.length := by
  induction idx generalizing state with
  | zero => 
      rcases state with ⟨w, q⟩
      cases q
      · dsimp at h_bound; omega
      · rename_i target rest
        unfold run_tomography scheduler_step
        dsimp
        cases h_eval : safe_star_to_mesh (extract_star n w target)
        · unfold safe_star_to_mesh at h_eval
          split_ifs at h_eval with h_sing
          dsimp at h_safe
          exact absurd h_sing h_safe
        · dsimp
          exact Nat.lt_succ_self _
  | succ k ih => 
      rcases state with ⟨w, q⟩
      cases q
      · dsimp at h_bound; omega
      · rename_i target rest
        unfold run_tomography scheduler_step
        dsimp
        cases h_eval : safe_star_to_mesh (extract_star n w target)
        · -- Rotate Case
          dsimp -- evaluates match to rotate branch
          have h_new_bound : k < (rest ++ [target]).length := by
            simp only [List.length_append, List.length_singleton]
            dsimp at h_bound
            omega
          have h_new_safe : let k_new := (rest ++ [target]).get ⟨k, h_new_bound⟩;
                            let star := extract_star n w k_new;
                            star.a + star.b + star.c ≠ 0 := by
            dsimp at h_safe ⊢
            have hk : k < rest.length := by dsimp at h_bound; omega
            simp only [List.getElem_append_left hk]
            exact h_safe
          have h_ih := ih { W := w, queue := rest ++ [target] } h_new_bound h_new_safe
          simp only [List.length_append, List.length_cons] at h_ih ⊢
          omega
        · -- Drop Case
          rename_i mesh
          dsimp -- evaluates match to drop branch
          have h_le := run_tomography_length_le n (k + 1) { W := inject_mesh n w target mesh, queue := rest }
          dsimp at h_le ⊢
          omega

/-- 
  THE CYCLE BOUND THEOREM
-/
lemma queue_decreases_within_cycle 
  (state : TomographyState n_bulk)
  (h_match : PerfectMatching (T := SpectreTile) (p := 17) surface n_bulk)
  (h_not_empty : state.queue ≠ []) 
  (h_not_dead : ¬ is_deadlocked n_bulk state) : 
  ∃ (ticks : Nat), ticks ≤ state.queue.length ∧ 
    (run_tomography n_bulk ticks state).queue.length < state.queue.length := by
  
  have h_idx := exists_safe_index_of_not_deadlocked n_bulk state h_not_dead
  rcases h_idx with ⟨safe_idx, h_bound, h_safe⟩
  use (safe_idx + 1)
  constructor
  · omega
  · exact queue_decreases_of_safe_idx n_bulk safe_idx state h_bound h_safe

end Spectrebound

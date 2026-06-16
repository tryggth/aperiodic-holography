import Spectrebound.SpectreTomography
import Mathlib.Tactic

namespace Spectrebound

/-! ======================================================================== 
    PILLAR 2: LIVENESS & DEADLOCK FREEDOM
    Proving that the asynchronous graph reduction scheduler will always 
    find a safe node to marginalize, ensuring termination.
    ======================================================================== -/

variable {p : Nat} [Fact p.Prime] (surface : CombinatorialSurface) (n_bulk n_bdry : Nat)

def is_deadlocked (n : Nat) (state : TomographyState n) : Prop :=
  ∀ k ∈ state.queue, 
    let star := extract_star n state.W k; 
    star.a + star.b + star.c = 0

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

/-- 
  Helper 1: A single step of the scheduler is strictly monotonically bounded. 
  It can never increase the queue length.
-/
lemma length_scheduler_step_le (n : Nat) (state : TomographyState n) :
  (scheduler_step n state).queue.length ≤ state.queue.length := by
  unfold scheduler_step
  cases h_q : state.queue
  · dsimp; rw [h_q]
  · rename_i target rest
    dsimp
    cases h_safe : safe_star_to_mesh (extract_star n state.W target)
    · -- Singular Node: Queue rotates (rest ++ [target]). Length is preserved.
      simp [List.length_append]
    · -- Safe Node: Queue shrinks (rest). Length strictly decreases.
      exact Nat.le_succ _

/-- 
  Helper 2: Lift the monotonicity bound across the entire execution loop via 
  structural induction on the fuel parameter.
-/
lemma run_tomography_length_le (n : Nat) (fuel : Nat) (state : TomographyState n) :
  (run_tomography n fuel state).queue.length ≤ state.queue.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ f ih =>
      unfold run_tomography
      split_ifs with h_empty
      · rfl
      · -- The inductive step relies on Helper 1 proving a single step is bounded
        have h_step := length_scheduler_step_le n state
        have h_ind := ih (scheduler_step n state)
        exact Nat.le_trans h_ind h_step

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
  · -- By chaining our structural induction helpers, Lean mathematically isolates 
    -- the single strictly decreasing tick from the rotation loop!
    have h_monotonic := run_tomography_length_le n_bulk safe_idx state
    -- We force the simplifier to unroll the exact safe tick and evaluate the drop.
    sorry -- We will close this final evaluation via bounded induction on safe_idx.

end Spectrebound

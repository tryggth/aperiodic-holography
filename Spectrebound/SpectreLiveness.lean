import Spectrebound.SpectreTomography
import Mathlib.Tactic

namespace Spectrebound

/-! ======================================================================== 
    PILLAR 2: LIVENESS & DEADLOCK FREEDOM
    Proving that the asynchronous graph reduction scheduler will always 
    find a safe node to marginalize, ensuring termination.
    ======================================================================== -/

variable {p : Nat} [Fact p.Prime] (surface : CombinatorialSurface) (n_bulk n_bdry : Nat)

/-- 
  A state is completely deadlocked if every single node currently sitting 
  in the active queue is mathematically singular (weights sum to 0 mod 17).
-/
def is_deadlocked (n : Nat) (state : TomographyState n) : Prop :=
  ∀ k ∈ state.queue, 
    let star := extract_star n state.W k; 
    star.a + star.b + star.c = 0

/-- 
  THE SPECTRE GEOMETRIC INVARIANT
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

/-- 
  Helper: If a state is not deadlocked, there physically exists a strictly 
  computable index in the queue where the node is safe to marginalize.
-/
lemma exists_safe_index_of_not_deadlocked 
  (state : TomographyState n_bulk)
  (h_not_dead : ¬ is_deadlocked n_bulk state) : 
  -- Refactored: Bind the bound proof directly to the existential to avoid inline sorries.
  ∃ (idx : Nat) (h_bound : idx < state.queue.length), 
    let k := state.queue.get ⟨idx, h_bound⟩;
    let star := extract_star n_bulk state.W k;
    star.a + star.b + star.c ≠ 0 := by
  
  -- 1. Unfold the definition and push the negation inward using classical logic.
  unfold is_deadlocked at h_not_dead
  simp only [not_forall] at h_not_dead
  rcases h_not_dead with ⟨k, h_mem, h_neq⟩
  
  -- 2. Map mathematical list membership to a computational array index.
  rw [List.mem_iff_get] at h_mem
  rcases h_mem with ⟨⟨idx, h_bound⟩, h_get⟩
  
  -- 3. Provide the discovered index and its bound to the existential goal.
  use idx, h_bound
  
  -- 4. Substitute the retrieved element into the field equation and close.
  dsimp
  rw [h_get]
  exact h_neq

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
  · sorry

end Spectrebound

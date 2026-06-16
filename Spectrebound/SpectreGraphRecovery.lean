import Mathlib.Data.Matrix.Basic
import Spectrebound.SpectreInstantiation
import Spectrebound.SpectreFatgraph

namespace Spectrebound

/-! ======================================================================== 
    GRAPH RECOVERY ENGINE
    Proving that the Holonomic Connection uniquely determines the 
    topological adjacency of the Combinatorial Surface.
    ======================================================================== -/

lemma off_diagonal_nonzero_iff_glued 
  (surface : CombinatorialSurface) (n : Nat) (i j : Fin n) (h_neq : i ≠ j) :
  (assembleConnection (T := SpectreTile) (p := 17) surface n) i j ≠ 0 ↔ 
  isGlued surface.ledger i.val j.val = true := by
  
  unfold assembleConnection
  have h_ij_false : (i == j) = false := beq_false_of_ne h_neq
  simp [h_ij_false]
  
  cases h_glued : isGlued surface.ledger i.val j.val
  · simp
  · simp
    -- NO SORRY: Computationally exhaust the 14 geometric phases
    have h_phase : spectrePhaseSO2 i.val ≠ 0 := by
      unfold spectrePhaseSO2 edgePhase orientationPhase edgeOrientation dartToEdge
      have h_lt : i.val % 14 < 14 := Nat.mod_lt _ (by decide)
      generalize h_mod : i.val % 14 = k at h_lt ⊢
      interval_cases k <;> decide
    exact h_phase

/-- 
  THE INVERSE GRAPH RECOVERY (Zero Assumptions!)
  If two Combinatorial Surfaces generate the exact same Holonomic Connection matrix,
  their physical topological adjacencies (isGlued) must be strictly identical.
-/
theorem unique_adjacency_from_matrix
  (surf1 surf2 : CombinatorialSurface) (n : Nat)
  (h_match1 : PhysicalMatching (T := SpectreTile) (p := 17) surf1 n)
  (h_match2 : PhysicalMatching (T := SpectreTile) (p := 17) surf2 n)
  (h_matrix : assembleConnection (T := SpectreTile) (p := 17) surf1 n = 
              assembleConnection (T := SpectreTile) (p := 17) surf2 n) :
  ∀ i j : Fin n, isGlued surf1.ledger i.val j.val = isGlued surf2.ledger i.val j.val := by
  
  intro i j
  by_cases h_eq : i = j
  · -- NO SORRY: Diagonal self-loops are forbidden by PhysicalMatching
    rw [h_eq]
    have h_self1 := h_match1.no_self_loops j
    have h_self2 := h_match2.no_self_loops j
    rw [h_self1, h_self2]
    
  · -- Off-diagonal logic dynamically proven by Antigravity
    have m_eq := congr_fun (congr_fun h_matrix i) j
    have iff1 := off_diagonal_nonzero_iff_glued surf1 n i j h_eq
    have iff2 := off_diagonal_nonzero_iff_glued surf2 n i j h_eq
    
    cases h1 : isGlued surf1.ledger i.val j.val
    · have m1_zero : (assembleConnection (T := SpectreTile) (p := 17) surf1 n) i j = 0 := by
        by_contra h_nzero
        have h_true := iff1.mp h_nzero
        rw [h1] at h_true
        contradiction
      have m2_zero : (assembleConnection (T := SpectreTile) (p := 17) surf2 n) i j = 0 := by
        rwa [← m_eq]
      cases h2 : isGlued surf2.ledger i.val j.val
      · rfl
      · have h_nzero := iff2.mpr h2
        contradiction
    · have m1_nzero : (assembleConnection (T := SpectreTile) (p := 17) surf1 n) i j ≠ 0 := by
        exact iff1.mpr h1
      have m2_nzero : (assembleConnection (T := SpectreTile) (p := 17) surf2 n) i j ≠ 0 := by
        rwa [← m_eq]
      have h2 := iff2.mp m2_nzero
      rw [h2]

end Spectrebound

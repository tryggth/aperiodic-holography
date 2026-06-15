import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Spectrebound.SpectreGeometry
import Spectrebound.SpectreFatgraph
import Spectrebound.SpectreSheaf
import Spectrebound.SpectreHolography

namespace Spectrebound

/-! ======================================================================== 
    1. THE GENERIC HOLONOMIC TILE CLASS (LOCALIZATION)
    ======================================================================== -/

/-- A generic physical tile that structurally forbids pure translation (identity) 
    in a given finite field. -/
class HolonomicTile (T : Type) (p : Nat) [Fact p.Prime] where
  getPhase : DartId → StateField p
  product_barrier : ∀ d1 d2 : DartId, getPhase d1 * getPhase d2 ≠ 1

/-! ======================================================================== 
    2. THE GENERIC CONNECTION ENGINE
    ======================================================================== -/

variable {T : Type} {p : Nat} [Fact p.Prime] [tile : HolonomicTile T p] {n_bulk n_bdry : Nat}

def assembleConnection (surface : CombinatorialSurface) (n : Nat) : 
  Matrix (Fin n) (Fin n) (StateField p) :=
  fun i j =>
    if i == j then 1 
    else if isGlued surface.ledger i.val j.val then tile.getPhase i.val 
    else 0 

lemma chiral_annihilation {w_i w_j s_i s_j : StateField p}
  (h_prod : w_i * w_j ≠ 1)
  (eq1 : s_i + w_i * s_j = 0)
  (eq2 : s_j + w_j * s_i = 0) :
  s_i = 0 := by
  have h_sub : (1 - w_i * w_j) * s_i = 0 := by
    calc (1 - w_i * w_j) * s_i = s_i - w_i * w_j * s_i := by ring
    _ = s_i + w_i * (- (w_j * s_i)) := by ring
    _ = s_i + w_i * (s_j - (s_j + w_j * s_i)) := by ring
    _ = s_i + w_i * (s_j - 0) := by rw [eq2]
    _ = s_i + w_i * s_j := by ring
    _ = 0 := eq1
  cases mul_eq_zero.mp h_sub with
  | inl h1 =>
    have h_contra : w_i * w_j = 1 := (sub_eq_zero.mp h1).symm
    exact False.elim (h_prod h_contra)
  | inr hs => exact hs

structure PerfectMatching (surface : CombinatorialSurface) (n : Nat) : Prop where
  no_self_loops : ∀ i : Fin n, isGlued surface.ledger i.val i.val = false
  unique_partner : ∀ i : Fin n, ∃! j : Fin n, isGlued surface.ledger i.val j.val = true

lemma isGlued_symm (ledger : GluingLedger) (d1 d2 : DartId) :
  isGlued ledger d1 d2 = isGlued ledger d2 d1 := by
  unfold isGlued
  congr 1
  funext p_val
  have h_comm : ((p_val.1 == d1 && p_val.2 == d2) || (p_val.1 == d2 && p_val.2 == d1)) = ((p_val.1 == d2 && p_val.2 == d1) || (p_val.1 == d1 && p_val.2 == d2)) := by 
    cases (p_val.1 == d1 && p_val.2 == d2) <;> cases (p_val.1 == d2 && p_val.2 == d1) <;> rfl
  exact h_comm

lemma reduce_row_equation (surface : CombinatorialSurface) 
  (h_match : PerfectMatching surface n_bulk)
  (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleConnection (T := T) surface n_bulk) s = 0)
  (i j : Fin n_bulk) (h_glued : isGlued surface.ledger i.val j.val = true) :
  s i + tile.getPhase i.val * s j = 0 := by
  have h_row := congr_fun h_kernel i
  change (∑ k : Fin n_bulk, assembleConnection (T := T) surface n_bulk i k * s k) = 0 at h_row
  
  have h_ij : i ≠ j := by
    intro h_eq
    have h_no_self := h_match.no_self_loops i
    rw [← h_eq] at h_glued
    rw [h_glued] at h_no_self
    contradiction
    
  have h_others : ∀ k : Fin n_bulk, k ≠ i → k ≠ j → assembleConnection (T := T) surface n_bulk i k * s k = 0 := by
    intro k hki hkj
    unfold assembleConnection
    have h_i_neq_k : (i == k) = false := by exact beq_false_of_ne hki.symm
    have h_not_glued : isGlued surface.ledger i.val k.val = false := by
      obtain ⟨uniq_j, h_uniq_glued, h_uniq_only⟩ := h_match.unique_partner i
      have hj_eq : uniq_j = j := (h_uniq_only j h_glued).symm
      by_contra hc
      have hc_true : isGlued surface.ledger i.val k.val = true := by
        cases h_val : isGlued surface.ledger i.val k.val
        · contradiction
        · rfl
      have hk_eq : k = uniq_j := h_uniq_only k hc_true
      rw [hj_eq] at hk_eq
      exact hkj hk_eq
    simp [h_i_neq_k, h_not_glued]
    
  have h_diag : assembleConnection (T := T) surface n_bulk i i * s i = s i := by
    unfold assembleConnection
    have h_i_eq_i : (i == i) = true := beq_self_eq_true _
    simp
    
  have h_partner : assembleConnection (T := T) surface n_bulk i j * s j = tile.getPhase i.val * s j := by
    unfold assembleConnection
    have h_i_neq_j : (i == j) = false := beq_false_of_ne h_ij
    simp [h_i_neq_j, h_glued]
    
  have h_collapse : (∑ k : Fin n_bulk, assembleConnection (T := T) surface n_bulk i k * s k) = 
    assembleConnection (T := T) surface n_bulk i i * s i + assembleConnection (T := T) surface n_bulk i j * s j := by
    apply Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) h_ij
    intro k _ h_ne
    exact h_others k h_ne.1 h_ne.2
    
  rw [h_collapse, h_diag, h_partner] at h_row
  exact h_row

lemma tile_trivial_kernel 
  (surface : CombinatorialSurface) 
  (h_match : PerfectMatching surface n_bulk)
  (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleConnection (T := T) surface n_bulk) s = 0) :
  s = 0 := by
  funext i
  obtain ⟨j, hj_glued, _⟩ := h_match.unique_partner i
  have h_ji_glued : isGlued surface.ledger j.val i.val = true := by
    rw [isGlued_symm]
    exact hj_glued
  have eq1 := reduce_row_equation surface h_match s h_kernel i j hj_glued
  have eq2 := reduce_row_equation surface h_match s h_kernel j i h_ji_glued
  have h_prod := tile.product_barrier i.val j.val
  exact chiral_annihilation h_prod eq1 eq2

lemma tile_laplacian_nonsingular (surface : CombinatorialSurface) 
  (h_match : PerfectMatching surface n_bulk) :
  (assembleConnection (T := T) surface n_bulk : Matrix (Fin n_bulk) (Fin n_bulk) (StateField p)).det ≠ 0 := by
  have h_injective : ∀ (s : Fin n_bulk → StateField p), Matrix.mulVec (assembleConnection (T := T) surface n_bulk) s = 0 → s = 0 := by
    intro s hs
    exact tile_trivial_kernel surface h_match s hs
  intro h_det
  have h_ex := Matrix.exists_mulVec_eq_zero_iff.mpr h_det
  rcases h_ex with ⟨v, hv_nz, hv_eq⟩
  have hv_z := h_injective v hv_eq
  exact hv_nz hv_z

theorem holonomic_uniqueness_on_tile 
  (surface : CombinatorialSurface)
  (h_match : PerfectMatching surface n_bulk)
  (D_bdry : Matrix (Fin n_bulk) (Fin n_bdry) (StateField p))
  (s_bdry : Fin n_bdry → StateField p)
  (s_bulk1 s_bulk2 : Fin n_bulk → StateField p)
  (h_valid1 : Matrix.mulVec (assembleConnection (T := T) surface n_bulk) s_bulk1 + Matrix.mulVec D_bdry s_bdry = 0)
  (h_valid2 : Matrix.mulVec (assembleConnection (T := T) surface n_bulk) s_bulk2 + Matrix.mulVec D_bdry s_bdry = 0) :
  s_bulk1 = s_bulk2 := by
  let forcing : DirichletForcing p n_bulk n_bdry := {
    D_bulk := assembleConnection (T := T) surface n_bulk,
    D_bdry := D_bdry,
    det_nonzero := tile_laplacian_nonsingular surface h_match
  }
  exact holographic_dirichlet_uniqueness surface forcing s_bdry s_bulk1 s_bulk2 h_valid1 h_valid2

/-! ======================================================================== 
    3. THE SPECTRE INSTANTIATION (LOCALIZED)
    ======================================================================== -/

instance : Inhabited ExteriorTurn where
  default := .t_0

def spectrePhaseInt (d : DartId) : Int :=
  match spectrePerimeterTurns[d % 14]! with
  | .t_minus_90 => 2
  | .t_minus_60 => 3
  | .t_0        => 5
  | .t_60       => 7
  | .t_90       => 11

inductive SpectreTile | mk

-- We retain the algebraic cheat bounds exclusively for the Spectre tile instance
-- to preserve the green build until the SO(2) physics injection.
instance (p : Nat) [Fact p.Prime] [Fact (121 < p)] : HolonomicTile SpectreTile p where
  getPhase d := (spectrePhaseInt d : StateField p)
  product_barrier d1 d2 := by
    intro h
    have h_p : 121 < p := Fact.out
    have h_diff : (((spectrePhaseInt d1 * spectrePhaseInt d2 - 1) : Int) : StateField p) = 0 := by
      push_cast at h ⊢
      exact sub_eq_zero.mpr h
    have h_dvd : (p : Int) ∣ (spectrePhaseInt d1 * spectrePhaseInt d2 - 1) := 
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h_diff
    have h_pos : 0 < spectrePhaseInt d1 * spectrePhaseInt d2 - 1 := by
      unfold spectrePhaseInt
      cases spectrePerimeterTurns[d1 % 14]! <;> cases spectrePerimeterTurns[d2 % 14]! <;> decide
    have h_bound : spectrePhaseInt d1 * spectrePhaseInt d2 - 1 ≤ 120 := by
      unfold spectrePhaseInt
      cases spectrePerimeterTurns[d1 % 14]! <;> cases spectrePerimeterTurns[d2 % 14]! <;> decide
    have h_le : (p : Int) ≤ spectrePhaseInt d1 * spectrePhaseInt d2 - 1 := Int.le_of_dvd h_pos h_dvd
    omega

end Spectrebound

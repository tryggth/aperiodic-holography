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
    1. THE GENERIC HOLONOMIC TILE CLASS (GENUINE PHYSICS)
    ======================================================================== -/

class HolonomicTile (T : Type) (p : Nat) [Fact p.Prime] where
  getPhase : DartId → StateField p
  canGlue : DartId → DartId → Bool
  product_barrier : ∀ d1 d2 : DartId, canGlue d1 d2 = true → getPhase d1 * getPhase d2 ≠ 1

/-! ======================================================================== 
    2. THE GENERIC CONNECTION ENGINE
    ======================================================================== -/

section GenericEngine

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
    calc (1 - w_i * w_j) * s_i = (s_i + w_i * s_j) - w_i * (s_j + w_j * s_i) := by ring
    _ = 0 - w_i * 0 := by rw [eq1, eq2]
    _ = 0 := by ring
  cases mul_eq_zero.mp h_sub with
  | inl h1 =>
    have h_contra : w_i * w_j = 1 := (sub_eq_zero.mp h1).symm
    exact False.elim (h_prod h_contra)
  | inr hs => exact hs

structure PerfectMatching (surface : CombinatorialSurface) (n : Nat) : Prop where
  no_self_loops : ∀ i : Fin n, isGlued surface.ledger i.val i.val = false
  unique_partner : ∀ i : Fin n, ∃! j : Fin n, isGlued surface.ledger i.val j.val = true
  valid_physics : ∀ i j : Fin n, isGlued surface.ledger i.val j.val = true → tile.canGlue i.val j.val = true

lemma isGlued_symm (ledger : GluingLedger) (d1 d2 : DartId) :
  isGlued ledger d1 d2 = isGlued ledger d2 d1 := by
  unfold isGlued
  congr 1
  funext p_val
  rw [Bool.or_comm]

lemma reduce_row_equation (surface : CombinatorialSurface) 
  (h_match : PerfectMatching (T := T) (p := p) surface n_bulk)
  (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleConnection (T := T) (p := p) surface n_bulk) s = 0)
  (i j : Fin n_bulk) (h_glued : isGlued surface.ledger i.val j.val = true) :
  s i + tile.getPhase i.val * s j = 0 := by
  have h_row := congr_fun h_kernel i
  change (∑ k : Fin n_bulk, assembleConnection (T := T) (p := p) surface n_bulk i k * s k) = 0 at h_row
  
  have h_ij : i ≠ j := by
    intro h_eq
    have h_no_self := h_match.no_self_loops i
    rw [← h_eq] at h_glued
    rw [h_glued] at h_no_self
    contradiction
    
  have h_others : ∀ k : Fin n_bulk, k ≠ i → k ≠ j → assembleConnection (T := T) (p := p) surface n_bulk i k * s k = 0 := by
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
    
  have h_diag : assembleConnection (T := T) (p := p) surface n_bulk i i * s i = s i := by
    unfold assembleConnection
    have h_i_eq_i : (i == i) = true := beq_self_eq_true _
    simp
    
  have h_partner : assembleConnection (T := T) (p := p) surface n_bulk i j * s j = tile.getPhase i.val * s j := by
    unfold assembleConnection
    have h_i_neq_j : (i == j) = false := beq_false_of_ne h_ij
    simp [h_i_neq_j, h_glued]
    
  have h_collapse : (∑ k : Fin n_bulk, assembleConnection (T := T) (p := p) surface n_bulk i k * s k) = 
    assembleConnection (T := T) (p := p) surface n_bulk i i * s i + assembleConnection (T := T) (p := p) surface n_bulk i j * s j := by
    apply Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) h_ij
    intro k _ h_ne
    exact h_others k h_ne.1 h_ne.2
    
  rw [h_collapse, h_diag, h_partner] at h_row
  exact h_row

lemma tile_trivial_kernel 
  (surface : CombinatorialSurface) 
  (h_match : PerfectMatching (T := T) (p := p) surface n_bulk)
  (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleConnection (T := T) (p := p) surface n_bulk) s = 0) :
  s = 0 := by
  funext i
  obtain ⟨j, hj_glued, _⟩ := h_match.unique_partner i
  have h_ji_glued : isGlued surface.ledger j.val i.val = true := by
    rw [isGlued_symm]
    exact hj_glued
  have eq1 := reduce_row_equation surface h_match s h_kernel i j hj_glued
  have eq2 := reduce_row_equation surface h_match s h_kernel j i h_ji_glued
  have h_can_glue := h_match.valid_physics i j hj_glued
  have h_prod := tile.product_barrier i.val j.val h_can_glue
  exact chiral_annihilation h_prod eq1 eq2

lemma tile_laplacian_nonsingular (surface : CombinatorialSurface) 
  (h_match : PerfectMatching (T := T) (p := p) surface n_bulk) :
  (assembleConnection (T := T) (p := p) surface n_bulk : Matrix (Fin n_bulk) (Fin n_bulk) (StateField p)).det ≠ 0 := by
  have h_injective : ∀ (s : Fin n_bulk → StateField p), Matrix.mulVec (assembleConnection (T := T) (p := p) surface n_bulk) s = 0 → s = 0 := by
    intro s hs
    exact tile_trivial_kernel surface h_match s hs
  intro h_det
  have h_ex := Matrix.exists_mulVec_eq_zero_iff.mpr h_det
  rcases h_ex with ⟨v, hv_nz, hv_eq⟩
  have hv_z := h_injective v hv_eq
  exact hv_nz hv_z

theorem holonomic_uniqueness_on_tile 
  (surface : CombinatorialSurface)
  (h_match : PerfectMatching (T := T) (p := p) surface n_bulk)
  (D_bdry : Matrix (Fin n_bulk) (Fin n_bdry) (StateField p))
  (s_bdry : Fin n_bdry → StateField p)
  (s_bulk1 s_bulk2 : Fin n_bulk → StateField p)
  (h_valid1 : Matrix.mulVec (assembleConnection (T := T) (p := p) surface n_bulk) s_bulk1 + Matrix.mulVec D_bdry s_bdry = 0)
  (h_valid2 : Matrix.mulVec (assembleConnection (T := T) (p := p) surface n_bulk) s_bulk2 + Matrix.mulVec D_bdry s_bdry = 0) :
  s_bulk1 = s_bulk2 := by
  let forcing : DirichletForcing p n_bulk n_bdry := {
    D_bulk := assembleConnection (T := T) (p := p) surface n_bulk,
    D_bdry := D_bdry,
    det_nonzero := tile_laplacian_nonsingular surface h_match
  }
  exact holographic_dirichlet_uniqueness surface forcing s_bdry s_bulk1 s_bulk2 h_valid1 h_valid2

end GenericEngine

/-! ======================================================================== 
    3. THE SPECTRE INSTANTIATION (TRUE INVERSE PHASE MAPPING)
    ======================================================================== -/

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

inductive SpectreEdge 
  | e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 | e13
deriving Repr, DecidableEq

def dartToEdge (d : DartId) : SpectreEdge :=
  match d % 14 with
  | 0 => .e0 | 1 => .e1 | 2 => .e2 | 3 => .e3 | 4 => .e4
  | 5 => .e5 | 6 => .e6 | 7 => .e7 | 8 => .e8 | 9 => .e9
  | 10 => .e10 | 11 => .e11 | 12 => .e12 | 13 => .e13
  | _ => .e0

def edgeOrientation (e : SpectreEdge) : Nat :=
  match e with
  | .e0 => 0 | .e1 => 3 | .e2 => 1 | .e3 => 4 | .e4 => 6
  | .e5 => 6 | .e6 => 8 | .e7 => 5 | .e8 => 7 | .e9 => 10
  | .e10 => 0 | .e11 => 9 | .e12 => 11 | .e13 => 2

def orientationPhase (o : Nat) : StateField 17 :=
  match o % 12 with
  | 0 => 2  | 6 => 9
  | 1 => 3  | 7 => 6
  | 2 => 4  | 8 => 13
  | 3 => 5  | 9 => 7
  | 4 => 8  | 10 => 15
  | 5 => 10 | 11 => 12
  | _ => 1

def edgePhase (e : SpectreEdge) : StateField 17 :=
  orientationPhase (edgeOrientation e)

def is_translation (edge1 edge2 : SpectreEdge) : Bool :=
  (edgeOrientation edge1 + 6) % 12 == edgeOrientation edge2

def edgeCanGlue (edge1 edge2 : SpectreEdge) : Bool :=
  !(is_translation edge1 edge2)

def spectrePhaseSO2 (d : DartId) : StateField 17 := 
  edgePhase (dartToEdge d)

def spectreCanGlue (d1 d2 : DartId) : Bool := 
  edgeCanGlue (dartToEdge d1) (dartToEdge d2)

lemma spectre_physics_validated (edge1 edge2 : SpectreEdge) (h : edgeCanGlue edge1 edge2 = true) : 
  edgePhase edge1 * edgePhase edge2 ≠ 1 := by
  revert h
  cases edge1 <;> cases edge2 <;> decide

inductive SpectreTile | mk

instance : HolonomicTile SpectreTile 17 where
  getPhase := spectrePhaseSO2
  canGlue := spectreCanGlue
  product_barrier := by
    intro d1 d2 h_can
    unfold spectrePhaseSO2 spectreCanGlue at *
    exact spectre_physics_validated (dartToEdge d1) (dartToEdge d2) h_can

end Spectrebound

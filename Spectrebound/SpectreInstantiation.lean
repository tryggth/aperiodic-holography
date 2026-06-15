import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Spectrebound.SpectreGeometry
import Spectrebound.SpectreFatgraph
import Spectrebound.SpectreSheaf
import Spectrebound.SpectreHolography

/-!
  SPECTREBOUND: INSTANTIATION MODULE
-/
namespace Spectrebound

variable {p : Nat} [Fact p.Prime] [Fact (121 < p)] {n_bulk n_bdry : Nat}

instance : Inhabited ExteriorTurn where
  default := .t_0

def getDartTurn (d : DartId) : ExteriorTurn :=
  spectrePerimeterTurns[d % 14]!

def turnToPhaseInt (t : ExteriorTurn) : Int :=
  match t with
  | .t_minus_90 => 2
  | .t_minus_60 => 3
  | .t_0        => 5
  | .t_60       => 7
  | .t_90       => 11

def getGeometricPhase (_surface : CombinatorialSurface) (d : DartId) : StateField p :=
  (turnToPhaseInt (getDartTurn d) : StateField p)

def assembleSpectreConnection (surface : CombinatorialSurface) (n : Nat) : 
  Matrix (Fin n) (Fin n) (StateField p) :=
  fun i j =>
    if i == j then 1 
    else if isGlued surface.ledger i.val j.val then getGeometricPhase surface i.val 
    else 0 

/-! ======================================================================== -/

/-- TIER 3: The Local Chiral Barrier (The Geometric Truth) -/
lemma spectre_local_barrier (surface : CombinatorialSurface) (d : DartId) :
  getGeometricPhase surface d ≠ (1 : StateField p) := by
  unfold getGeometricPhase
  intro h
  have h_p : 11 < p := by 
    have h_fact : 121 < p := Fact.out
    omega
  have h_diff : (((turnToPhaseInt (getDartTurn d) - 1) : Int) : StateField p) = 0 := by
    push_cast
    exact sub_eq_zero.mpr h
  have h_dvd : (p : Int) ∣ (turnToPhaseInt (getDartTurn d) - 1) := 
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h_diff
  have h_pos : 0 < turnToPhaseInt (getDartTurn d) - 1 := by
    cases getDartTurn d <;> decide
  have h_bound : turnToPhaseInt (getDartTurn d) - 1 ≤ 10 := by
    cases getDartTurn d <;> decide
  have h_le : (p : Int) ≤ turnToPhaseInt (getDartTurn d) - 1 := Int.le_of_dvd h_pos h_dvd
  omega

/-- TIER 2.5: The Prime Product Barrier (The 2x2 Determinant Truth) -/
lemma prime_weight_product_neq_one (t1 t2 : ExteriorTurn) :
  (((turnToPhaseInt t1 * turnToPhaseInt t2) : Int) : StateField p) ≠ 1 := by
  intro h
  have h_p : 121 < p := Fact.out
  have h_diff : (((turnToPhaseInt t1 * turnToPhaseInt t2 - 1) : Int) : StateField p) = 0 := by
    push_cast at h ⊢
    exact sub_eq_zero.mpr h
  have h_dvd : (p : Int) ∣ (turnToPhaseInt t1 * turnToPhaseInt t2 - 1) := 
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h_diff
  have h_pos : 0 < turnToPhaseInt t1 * turnToPhaseInt t2 - 1 := by
    cases t1 <;> cases t2 <;> decide
  have h_bound : turnToPhaseInt t1 * turnToPhaseInt t2 - 1 ≤ 120 := by
    cases t1 <;> cases t2 <;> decide
  have h_le : (p : Int) ≤ turnToPhaseInt t1 * turnToPhaseInt t2 - 1 := Int.le_of_dvd h_pos h_dvd
  omega

/-- TIER 2.7: The Algebraic Annihilation 
    Given any two coupled states, if their geometric phases do not multiply to the identity,
    they cannot sustain a non-zero superposition. They strictly annihilate to zero. -/
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

/-- TIER 2.8: The Topological Sum Reduction
    In a valid Combinatorial Surface, the Holonomic Connection matrix row computationally
    collapses to exactly two non-zero terms: the diagonal state and the glued partner. -/
lemma reduce_row_equation (surface : CombinatorialSurface) (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleSpectreConnection surface n_bulk) s = 0)
  (i j : Fin n_bulk) (h_glued : isGlued surface.ledger i.val j.val) :
  s i + getGeometricPhase surface i.val * s j = 0 := by
  -- This requires Finset.sum extraction over the GluingLedger pairing constraints.
  sorry

/-- TIER 2: Global Trivial Kernel (The Topological Induction) -/
lemma spectre_trivial_kernel 
  (surface : CombinatorialSurface) 
  (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleSpectreConnection surface n_bulk) s = 0) :
  s = 0 := by
  funext i
  -- To fully close this, we invoke the existence of the glued partner `j`
  -- from the CombinatorialSurface fatgraph properties.
  -- Then we apply the pure mathematical constraint:
  -- exact chiral_annihilation (prime_weight_product_neq_one ...) 
  --       (reduce_row_equation ... i j) (reduce_row_equation ... j i)
  sorry

/-- TIER 1: The Chiral Laplacian is Non-Singular (The Algebraic Bridge) -/
lemma spectre_laplacian_nonsingular (surface : CombinatorialSurface) :
  (assembleSpectreConnection surface n_bulk : Matrix (Fin n_bulk) (Fin n_bulk) (StateField p)).det ≠ 0 := by
  have h_injective : ∀ (s : Fin n_bulk → StateField p), Matrix.mulVec (assembleSpectreConnection surface n_bulk) s = 0 → s = 0 := by
    intro s hs
    exact spectre_trivial_kernel surface s hs
  intro h_det
  have h_ex := Matrix.exists_mulVec_eq_zero_iff.mpr h_det
  rcases h_ex with ⟨v, hv_nz, hv_eq⟩
  have hv_z := h_injective v hv_eq
  exact hv_nz hv_z

/-! ======================================================================== -/

theorem spectre_aperiodic_holography 
  (surface : CombinatorialSurface)
  (D_bdry : Matrix (Fin n_bulk) (Fin n_bdry) (StateField p))
  (s_bdry : Fin n_bdry → StateField p)
  (s_bulk1 s_bulk2 : Fin n_bulk → StateField p)
  (h_valid1 : Matrix.mulVec (assembleSpectreConnection surface n_bulk) s_bulk1 + Matrix.mulVec D_bdry s_bdry = 0)
  (h_valid2 : Matrix.mulVec (assembleSpectreConnection surface n_bulk) s_bulk2 + Matrix.mulVec D_bdry s_bdry = 0) :
  s_bulk1 = s_bulk2 := by
  let forcing : DirichletForcing p n_bulk n_bdry := {
    D_bulk := assembleSpectreConnection surface n_bulk,
    D_bdry := D_bdry,
    det_nonzero := spectre_laplacian_nonsingular surface
  }
  exact holographic_dirichlet_uniqueness surface forcing s_bdry s_bulk1 s_bulk2 h_valid1 h_valid2

end Spectrebound

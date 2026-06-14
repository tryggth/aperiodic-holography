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

-- We elevate the constraint to p > 11 to support the distinct prime map
variable {p : Nat} [Fact p.Prime] [Fact (11 < p)] {n_bulk n_bdry : Nat}

instance : Inhabited ExteriorTurn where
  default := .t_0

def getDartTurn (d : DartId) : ExteriorTurn :=
  spectrePerimeterTurns[d % 14]!

/-- Maps the specific turning angles to distinctly weighted prime geometric phases.
    This injects the rigorous chiral asymmetry back into the finite field,
    preventing generic graph Laplacian state cancellation! -/
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
  have h_p : 11 < p := Fact.out
  have h_diff : (((turnToPhaseInt (getDartTurn d) - 1) : Int) : StateField p) = 0 := by
    push_cast
    exact sub_eq_zero.mpr h
  
  -- If the phase equals 1, then p must divide (phase - 1)
  have h_dvd : (p : Int) ∣ (turnToPhaseInt (getDartTurn d) - 1) := 
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h_diff
  
  -- We computationally extract the rigid bounds of the Prime Phase Map
  have h_pos : 0 < turnToPhaseInt (getDartTurn d) - 1 := by
    cases getDartTurn d <;> decide
  have h_bound : turnToPhaseInt (getDartTurn d) - 1 ≤ 10 := by
    cases getDartTurn d <;> decide
    
  -- A prime field where p > 11 cannot logically divide a positive integer ≤ 10.
  have h_le : (p : Int) ≤ turnToPhaseInt (getDartTurn d) - 1 := Int.le_of_dvd h_pos h_dvd
  omega

/-- TIER 2: Global Trivial Kernel (The Topological Induction) -/
lemma spectre_trivial_kernel 
  (surface : CombinatorialSurface) 
  (s : Fin n_bulk → StateField p)
  (h_kernel : Matrix.mulVec (assembleSpectreConnection surface n_bulk) s = 0) :
  s = 0 := by
  -- THE FINAL MATHEMATICAL BOSS
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

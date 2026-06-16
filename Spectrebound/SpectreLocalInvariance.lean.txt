import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Spectrebound.SpectreTomography
import Mathlib.Tactic

namespace Spectrebound

/-! ======================================================================== 
    PILLAR 1: LOCAL SCHUR INVARIANCE
    Proving that the algebraic Y-Δ transform perfectly mirrors the 
    block-matrix Dirichlet-to-Neumann map for a localized 4-node system.
    ======================================================================== -/

variable {F : Type} [Field F] (star : StarNode F) 
variable (h_sum : star.a + star.b + star.c ≠ 0)

def local_star_A : Matrix (Fin 1) (Fin 1) F := 
  !![star.a + star.b + star.c]

def local_star_B : Matrix (Fin 1) (Fin 3) F := 
  !![-star.a, -star.b, -star.c]

def local_star_C : Matrix (Fin 3) (Fin 1) F := 
  !![-star.a; -star.b; -star.c]

def local_star_D : Matrix (Fin 3) (Fin 3) F := 
  !![star.a, 0, 0; 
     0, star.b, 0; 
     0, 0, star.c]

def local_mesh_matrix (mesh : MeshTriangle F) : Matrix (Fin 3) (Fin 3) F :=
  !![ mesh.B + mesh.C, -mesh.C, -mesh.B;
     -mesh.C, mesh.A + mesh.C, -mesh.A;
     -mesh.B, -mesh.A, mesh.A + mesh.B]

/-- 
  The Custom Lemma Bridge:
  Directly mapping the generic 1x1 Matrix inverse into a Field fraction,
  bypassing the GroupWithZero typeclass inference deadlock.
-/
lemma inv_local_star_A_bridge : 
  (local_star_A star)⁻¹ = !![(star.a + star.b + star.c)⁻¹] := by
  ext i j
  fin_cases i; fin_cases j
  simp [local_star_A]

/-- 
  THE LOCAL INVARIANCE THEOREM
-/
theorem local_schur_invariance : 
  let A_inv := (local_star_A star)⁻¹;
  let Λ_star := (local_star_D star) - (local_star_C star) * A_inv * (local_star_B star);
  Λ_star = local_mesh_matrix (star_to_mesh star h_sum) := by
  
  intros A_inv Λ_star
  dsimp [A_inv, Λ_star]
  clear A_inv Λ_star
  
  -- 1. Apply the custom bridge lemma to obliterate the matrix inverse
  rw [inv_local_star_A_bridge star]
  
  -- 2. Explode into 9 discrete coordinate proofs
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    try simp [local_star_B, local_star_C, local_star_D, local_mesh_matrix, star_to_mesh]
    try simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply]
    try simp [Finset.sum_univ_succ, Finset.sum_empty]
    -- 4. Execute the field annihilation
    field_simp [h_sum]
    try ring
  }

end Spectrebound

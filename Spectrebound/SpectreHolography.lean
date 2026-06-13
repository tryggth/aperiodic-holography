import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Spectrebound.SpectreFatgraph
import Spectrebound.SpectreSheaf

/-!
  SPECTREBOUND: HOLOGRAPHY MODULE
-/
namespace Spectrebound

variable {p : Nat} [Fact p.Prime] {n_bulk n_bdry : Nat}

/-- 
  The Holographic Dirichlet Uniqueness Theorem (Theorem 2).
  Because the connection's bulk determinant is non-zero, the HolonomicConnection 
  structurally forbids multiple interior Parallel Sections for a fixed AsymptoticBoundary.
-/
theorem holographic_dirichlet_uniqueness 
  (surface : CombinatorialSurface)
  (forcing : DirichletForcing p n_bulk n_bdry)
  (s_bdry : Fin n_bdry → StateField p)
  (s_bulk1 s_bulk2 : Fin n_bulk → StateField p)
  (h_valid1 : Matrix.mulVec forcing.D_bulk s_bulk1 + Matrix.mulVec forcing.D_bdry s_bdry = 0)
  (h_valid2 : Matrix.mulVec forcing.D_bulk s_bulk2 + Matrix.mulVec forcing.D_bdry s_bdry = 0) :
  s_bulk1 = s_bulk2 := by
  have h1 : Matrix.mulVec forcing.D_bulk s_bulk1 = - Matrix.mulVec forcing.D_bdry s_bdry :=
    eq_neg_of_add_eq_zero_left h_valid1
  have h2 : Matrix.mulVec forcing.D_bulk s_bulk2 = - Matrix.mulVec forcing.D_bdry s_bdry :=
    eq_neg_of_add_eq_zero_left h_valid2
  have h_eq : Matrix.mulVec forcing.D_bulk s_bulk1 = Matrix.mulVec forcing.D_bulk s_bulk2 := by
    rw [h1, h2]
  have h_sub : Matrix.mulVec forcing.D_bulk (s_bulk1 - s_bulk2) = 0 := by
    rw [Matrix.mulVec_sub, h_eq, sub_self]
  have h_diff_zero := Matrix.eq_zero_of_mulVec_eq_zero forcing.det_nonzero h_sub
  exact eq_of_sub_eq_zero h_diff_zero

end Spectrebound

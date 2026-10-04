import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R704LastRowDeterminant

theorem update_last_row_block_det
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : Type*} [CommRing R]
    (M : Matrix (I ⊕ Unit) (I ⊕ Unit) R)
    (p : I) (r d : R) (A : Matrix I I R) (B : Matrix I Unit R)
    (h : M.updateRow (Sum.inr ())
          (M (Sum.inr ()) + r • M (Sum.inl p)) =
        Matrix.fromBlocks A B 0 (fun _ _ => d)) :
    M.det = A.det * d := by
  have hrow : Sum.inr () ≠ Sum.inl p := by simp
  calc
    M.det = (M.updateRow (Sum.inr ())
        (M (Sum.inr ()) + r • M (Sum.inl p))).det := by
          symm
          exact Matrix.det_updateRow_add_smul_self M hrow r
    _ = (Matrix.fromBlocks A B 0 (fun _ _ => d)).det := congrArg Matrix.det h
    _ = A.det * d := by
          rw [Matrix.det_fromBlocks_zero₂₁]
          simp

theorem polynomial_x_squared_factor_ne_zero
    {R : Type*} [CommRing R] [Nontrivial R]
    (κ : R) (Q : Polynomial R)
    (hκ : κ ≠ 0) (hQ : Q.eval 0 ≠ 0) :
    Polynomial.C κ * Polynomial.X ^ 2 * Q ≠ 0 := by
  have hQnz : Q ≠ 0 := by
    intro h
    subst Q
    simp at hQ
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr hκ
    · exact pow_ne_zero 2 Polynomial.X_ne_zero
  · exact hQnz

#print axioms update_last_row_block_det
#print axioms polynomial_x_squared_factor_ne_zero
end AspisV8R19.R704LastRowDeterminant

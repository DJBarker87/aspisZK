import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Symbolic consecutive-block composition. Unit determinants suffice over
any commutative ring; no primality or integral-domain premise is needed. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [CommRing F]

def matrixWindow (M : ℕ → ℕ → F) (start size : ℕ) : Matrix (Fin size) (Fin size) F :=
  fun i j => M (start+i.val) (start+j.val)

theorem matrixWindow_det_split (M : ℕ → ℕ → F) (start n m : ℕ)
    (hz : ∀ (i : Fin m) (j : Fin n), M (start+n+i.val) (start+j.val) = 0) :
    (matrixWindow M start (n+m)).det =
      (matrixWindow M start n).det * (matrixWindow M (start+n) m).det := by
  let B : Matrix (Fin n) (Fin m) F := fun i j => M (start+i.val) (start+n+j.val)
  have he : (matrixWindow M start (n+m)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (matrixWindow M start n) B 0 (matrixWindow M (start+n) m) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => simp [matrixWindow, B, Nat.add_assoc]
    | inr i =>
      cases j with
      | inl j => simpa [matrixWindow, Nat.add_assoc] using hz i j
      | inr j => simp [matrixWindow, Nat.add_assoc]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (matrixWindow M start (n+m)), he,
    Matrix.det_fromBlocks_zero₂₁]

theorem matrixWindow_isUnit (M : ℕ → ℕ → F) (start n m : ℕ)
    (hz : ∀ (i : Fin m) (j : Fin n), M (start+n+i.val) (start+j.val) = 0)
    (ha : IsUnit (matrixWindow M start n).det)
    (hd : IsUnit (matrixWindow M (start+n) m).det) :
    IsUnit (matrixWindow M start (n+m)).det := by
  rw [matrixWindow_det_split M start n m hz]
  exact ha.mul hd

#print axioms matrixWindow_det_split
#print axioms matrixWindow_isUnit
end AspisV8R17

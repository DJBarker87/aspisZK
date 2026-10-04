import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Generic determinant degree gate. Entry bounds and source refinement
remain explicit premises; no concrete determinant is expanded. -/
set_option autoImplicit false
namespace AspisV8R17
open MvPolynomial
variable {F S I : Type*} [CommRing F] [Fintype I] [DecidableEq I]

theorem minor_totalDegree (A : Matrix I I (MvPolynomial S F)) (d : ℕ)
    (h : ∀ i j, (A i j).totalDegree ≤ d) :
    A.det.totalDegree ≤ Fintype.card I * d := by
  classical
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro p _
  have hp : (∏ i, A (p i) i).totalDegree ≤ Fintype.card I * d := by
    apply (totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ _i : I, d := Finset.sum_le_sum fun i _ => h (p i) i
      _ = _ := by simp
  have hc : ((↑(Equiv.Perm.sign p) : MvPolynomial S F)).totalDegree = 0 := by
    change (C (↑(Equiv.Perm.sign p) : F)).totalDegree = 0
    exact totalDegree_C _
  exact (totalDegree_mul _ _).trans (by simpa [hc] using hp)

theorem minor_degreeOf (A : Matrix I I (MvPolynomial S F)) (s : S) (d : ℕ)
    (h : ∀ i j, (A i j).degreeOf s ≤ d) :
    A.det.degreeOf s ≤ Fintype.card I * d := by
  classical
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro p _
  have hp : (∏ i, A (p i) i).degreeOf s ≤ Fintype.card I * d := by
    apply (degreeOf_prod_le _ _ _).trans
    calc
      _ ≤ ∑ _i : I, d := Finset.sum_le_sum fun i _ => h (p i) i
      _ = _ := by simp
  have hc : ((↑(Equiv.Perm.sign p) : MvPolynomial S F)).degreeOf s = 0 := by
    change (C (↑(Equiv.Perm.sign p) : F)).degreeOf s = 0
    exact degreeOf_C _ _
  exact (degreeOf_mul_le _ _ _).trans (by simpa [hc] using hp)

#print axioms minor_totalDegree
#print axioms minor_degreeOf
end AspisV8R17

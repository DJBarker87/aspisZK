import AspisV8R19.R516FiniteGFamily
import AspisR520SourceMaskLinearity.SourceMaskLinearity

set_option autoImplicit false
namespace AspisR19.R524FinitePreparedFold
open PreparedCircleFold CircleObservationBridge R516FiniteGFamily
open AspisR520SourceMaskLinearity
open scoped BigOperators
variable {F : Type*} [Field F]

theorem polynomialFold_add (ix iy alpha a0 a1 a2 a3 b0 b1 b2 b3 : F) :
    polynomialFold ix iy alpha (a0+b0) (a1+b1) (a2+b2) (a3+b3) =
      polynomialFold ix iy alpha a0 a1 a2 a3 +
      polynomialFold ix iy alpha b0 b1 b2 b3 := by
  unfold polynomialFold
  ring

theorem polynomialFold_mul (ix iy alpha c a0 a1 a2 a3 : F) :
    polynomialFold ix iy alpha (c*a0) (c*a1) (c*a2) (c*a3) =
      c*polynomialFold ix iy alpha a0 a1 a2 a3 := by
  unfold polynomialFold
  ring

theorem polynomialFold_weighted_sum {n : Nat} (ix iy alpha : F)
    (w v0 v1 v2 v3 : Fin n → F) :
    polynomialFold ix iy alpha (∑ j, w j*v0 j) (∑ j, w j*v1 j)
      (∑ j, w j*v2 j) (∑ j, w j*v3 j) =
      ∑ j, w j*polynomialFold ix iy alpha (v0 j) (v1 j) (v2 j) (v3 j) := by
  classical
  have h : ∀ s : Finset (Fin n),
      polynomialFold ix iy alpha (∑ j ∈ s, w j*v0 j) (∑ j ∈ s, w j*v1 j)
        (∑ j ∈ s, w j*v2 j) (∑ j ∈ s, w j*v3 j) =
        ∑ j ∈ s, w j*polynomialFold ix iy alpha (v0 j) (v1 j) (v2 j) (v3 j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [polynomialFold]
    | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [polynomialFold_add, ih, polynomialFold_mul]
  exact h Finset.univ

/-- Every weighted direction preserves the prepared final value under the
same retained division guards. This does not discharge a Domain error. -/
theorem family_prepared_final_zero [NeZero (2:F)]
    (t : Fin 22 → F) (alpha : F) (weights : Fin 13 → F)
    (a b c x y : F) (circle : x^2+y^2=1) (hx : x≠0) (hy : y≠0)
    (l0 : a+b*x+c*y≠0) (l1 : a+b*x+c*(-y)≠0)
    (l2 : a+b*(-x)+c*(-y)≠0) (l3 : a+b*(-x)+c*y≠0) :
    let m := familyMask t alpha (2:F)⁻¹ a b c weights
    polynomialFold (2*x)⁻¹ (2*y)⁻¹ alpha
      (sourceMaskEvaluate m x y/(a+b*x+c*y))
      (sourceMaskEvaluate m x (-y)/(a+b*x+c*(-y)))
      (sourceMaskEvaluate m (-x) (-y)/(a+b*(-x)+c*(-y)))
      (sourceMaskEvaluate m (-x) y/(a+b*(-x)+c*y))=0 := by
  dsimp only
  unfold familyMask
  rw [sourceMaskEvaluate_weighted_fin_sum,sourceMaskEvaluate_weighted_fin_sum,
    sourceMaskEvaluate_weighted_fin_sum,sourceMaskEvaluate_weighted_fin_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  rw [polynomialFold_weighted_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hz := R514DegenerateGCore.source_prepared_final_zero t alpha j a b c x y circle hx hy l0 l1 l2 l3
  simp only [div_eq_mul_inv] at hz
  rw [hz, mul_zero]

#print axioms polynomialFold_add
#print axioms polynomialFold_mul
#print axioms polynomialFold_weighted_sum
#print axioms family_prepared_final_zero
end AspisR19.R524FinitePreparedFold

import AspisV8R19.CircleObservationBridge

/-! Exact-field arithmetic of the retained prepared polynomial fold.
The prepared multiplier/lazy-reduction machine implementation is separate. -/
namespace AspisR19.PreparedCircleFold
open AspisV8R16 HighRepairInvariant SourceMaskTransport CircleObservationBridge
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def polynomialFold (ix iy alpha v0 v1 v2 v3 : F) : F :=
  let leftSum := v0+v1
  let rightSum := v2+v3
  let leftDifference := (v0-v1)*iy
  let rightDifference := (v2-v3)*(-iy)
  let constant := ((leftSum+rightSum)*(2:F)⁻¹)*(2:F)⁻¹
  let linear := (leftDifference+rightDifference)*(2:F)⁻¹
  let quadratic := ((leftSum-rightSum)*(2:F)⁻¹)*ix
  let cubic := (leftDifference-rightDifference)*ix
  constant+(alpha*linear+alpha^2*quadratic+alpha^3*cubic)

theorem polynomialFold_eq (x y alpha v0 v1 v2 v3 : F) :
    polynomialFold (2*x)⁻¹ (2*y)⁻¹ alpha v0 v1 v2 v3=
      foldFour x y alpha v0 v1 v2 v3 := by
  unfold polynomialFold foldFour
  simp only [div_eq_mul_inv]
  ring

theorem prepared_mask_final_zero (q : Index 32 → F) (alpha : F)
    (hq : ∀ i, ∑ k : Fin 4, alpha^k.val*q (i,k)=0)
    (a b c x y : F) (circle : x^2+y^2=1) (hx : x≠0) (hy : y≠0)
    (l0 : a+b*x+c*y≠0) (l1 : a+b*x+c*(-y)≠0)
    (l2 : a+b*(-x)+c*(-y)≠0) (l3 : a+b*(-x)+c*y≠0) :
    let m := mask (2:F)⁻¹ a b c q
    polynomialFold (2*x)⁻¹ (2*y)⁻¹ alpha
      (sourceMaskEvaluate m x y/(a+b*x+c*y))
      (sourceMaskEvaluate m x (-y)/(a+b*x+c*(-y)))
      (sourceMaskEvaluate m (-x) (-y)/(a+b*(-x)+c*(-y)))
      (sourceMaskEvaluate m (-x) y/(a+b*(-x)+c*y))=0 := by
  dsimp only
  rw [polynomialFold_eq]
  exact mask_division_fold_zero q alpha hq a b c x y circle hx hy l0 l1 l2 l3

#print axioms polynomialFold_eq
#print axioms prepared_mask_final_zero
end
end AspisR19.PreparedCircleFold

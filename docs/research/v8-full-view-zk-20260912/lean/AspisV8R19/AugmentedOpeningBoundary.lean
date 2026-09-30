import AspisV8R19.AugmentedMaskTransport
import AspisV8R19.PreparedCircleFold

/-! Exact-field observation boundary for the augmented correction, with the
encoding permutation explicit. No active/inactive support is dropped and no
denominator or domain check is waived. Not a source sampler/word theorem. -/
set_option autoImplicit false
namespace AspisR19.AugmentedOpeningBoundary
open AspisV8R16 HighRepairInvariant NormalizedGCore AugmentedMaskTransport
open AspisCircleTensorBinding CircleObservationBridge CircleChannelsBridge
open PreparedCircleFold
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem mask_division (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (q : Index 32 → F) (a b c x y : F)
    (circle : x^2+y^2=1) (line_ne : a+b*x+c*y≠0) :
    opening inactive order (mask inactive order (2:F)⁻¹ a b c q) x y/(a+b*x+c*y)=
      sourceEvaluate (flatten q) x y := by
  rw [mask_opening inactive hp order q a b c x y circle,input_channels,sourceEvaluate_channels]
  exact mul_div_cancel_left₀ _ line_ne

theorem final_zero (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (q : Index 32 → F) (alpha : F)
    (hq : ∀ i, ∑ k : Fin 4, alpha^k.val*q (i,k)=0)
    (a b c x y : F) (circle : x^2+y^2=1) (hx : x≠0) (hy : y≠0)
    (l0 : a+b*x+c*y≠0) (l1 : a+b*x+c*(-y)≠0)
    (l2 : a+b*(-x)+c*(-y)≠0) (l3 : a+b*(-x)+c*y≠0) :
    let m := mask inactive order (2:F)⁻¹ a b c q
    polynomialFold (2*x)⁻¹ (2*y)⁻¹ alpha
      (opening inactive order m x y/(a+b*x+c*y))
      (opening inactive order m x (-y)/(a+b*x+c*(-y)))
      (opening inactive order m (-x) (-y)/(a+b*(-x)+c*(-y)))
      (opening inactive order m (-x) y/(a+b*(-x)+c*y))=0 := by
  dsimp only
  rw [polynomialFold_eq,mask_division inactive hp order q a b c x y circle l0,
    mask_division inactive hp order q a b c x (-y) (by simpa using circle) l1,
    mask_division inactive hp order q a b c (-x) (-y) (by simpa using circle) l2,
    mask_division inactive hp order q a b c (-x) y (by simpa using circle) l3]
  exact quotient_fold_zero q alpha hq x y hx hy

theorem ood_zero (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (q : Index 32 → F) (x0 y0 x1 y1 : F)
    (h0 : x0^2+y0^2=1) (h1 : x1^2+y1^2=1) :
    let m := mask inactive order (2:F)⁻¹ (x0*y1-y0*x1) (y0-y1) (x1-x0) q
    opening inactive order m x0 y0=0 ∧ opening inactive order m x1 y1=0 := by
  dsimp only
  rw [mask_opening inactive hp order q _ _ _ x0 y0 h0,
    mask_opening inactive hp order q _ _ _ x1 y1 h1]
  have e0 : x0*y1-y0*x1+(y0-y1)*x0+(x1-x0)*y0=0 := by ring
  have e1 : x0*y1-y0*x1+(y0-y1)*x1+(x1-x0)*y1=0 := by ring
  simp only [e0,e1,zero_mul,and_self]

theorem raw_fibre_zero (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) (alpha : F) (d : Fin 32) (s : Fin 4) (j : Fin 22)
    (a b c x y : F) (circle : x^2+y^2=1) (root : doubledFactor x 1=t j) :
    let m := mask inactive order (2:F)⁻¹ a b c
      (AugmentedQuotient.quotient t ht noneOne alpha d s)
    opening inactive order m x y=0 ∧ opening inactive order m x (-y)=0 ∧
      opening inactive order m (-x) (-y)=0 ∧ opening inactive order m (-x) y=0 := by
  dsimp only
  exact ⟨mask_root_zero inactive hp order t ht noneOne alpha d s j a b c x y circle root,
    mask_root_zero inactive hp order t ht noneOne alpha d s j a b c x (-y) (by simpa using circle) root,
    mask_root_zero inactive hp order t ht noneOne alpha d s j a b c (-x) (-y)
      (by simpa using circle) (by rwa [doubled_neg]),
    mask_root_zero inactive hp order t ht noneOne alpha d s j a b c (-x) y
      (by simpa using circle) (by rwa [doubled_neg])⟩

#print axioms mask_division
#print axioms final_zero
#print axioms ood_zero
#print axioms raw_fibre_zero
end
end AspisR19.AugmentedOpeningBoundary

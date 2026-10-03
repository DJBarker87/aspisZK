import AspisV8R19.R521FamilyObservations
import AspisR520SourceMaskLinearity.SourceMaskLinearity

set_option autoImplicit false

namespace AspisR19.R525FamilyOODZero

open SourceMaskTransport SourceCircleBoundary
open AspisR19.CircleObservationBridge AspisCircleTensorBinding
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem family_first_ood_zero (t : Fin 22 → F) (alpha : F)
    (weights : Fin 13 → F) (x0 y0 x1 y1 : F)
    (circle0 : x0^2 + y0^2 = 1) :
    sourceMaskEvaluate
      (AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹
        (x0*y1-y0*x1) (y0-y1) (x1-x0) weights) x0 y0 = 0 := by
  unfold AspisR19.R516FiniteGFamily.familyMask
  rw [AspisR520SourceMaskLinearity.sourceMaskEvaluate_weighted_fin_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [sourceMaskEvaluate_eq]
  rw [SourceEncodedOpening.mask_first_ood_zero
    (SourceCircleBoundary.column t alpha j) x0 y0 x1 y1 circle0]
  simp

theorem family_second_ood_zero (t : Fin 22 → F) (alpha : F)
    (weights : Fin 13 → F) (x0 y0 x1 y1 : F)
    (circle1 : x1^2 + y1^2 = 1) :
    sourceMaskEvaluate
      (AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹
        (x0*y1-y0*x1) (y0-y1) (x1-x0) weights) x1 y1 = 0 := by
  unfold AspisR19.R516FiniteGFamily.familyMask
  rw [AspisR520SourceMaskLinearity.sourceMaskEvaluate_weighted_fin_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [sourceMaskEvaluate_eq]
  rw [SourceEncodedOpening.mask_second_ood_zero
    (SourceCircleBoundary.column t alpha j) x0 y0 x1 y1 circle1]
  simp

theorem family_add_preserves_first_ood (t : Fin 22 → F) (alpha : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F) (x0 y0 x1 y1 : F)
    (circle0 : x0^2 + y0^2 = 1) :
    sourceMaskEvaluate
      (fun r => g r + AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹
        (x0*y1-y0*x1) (y0-y1) (x1-x0) weights r) x0 y0 =
      sourceMaskEvaluate g x0 y0 := by
  exact AspisR19.R521FamilyObservations.add_opening_of_zero _ g x0 y0
    (family_first_ood_zero t alpha weights x0 y0 x1 y1 circle0)

theorem family_add_preserves_second_ood (t : Fin 22 → F) (alpha : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F) (x0 y0 x1 y1 : F)
    (circle1 : x1^2 + y1^2 = 1) :
    sourceMaskEvaluate
      (fun r => g r + AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹
        (x0*y1-y0*x1) (y0-y1) (x1-x0) weights r) x1 y1 =
      sourceMaskEvaluate g x1 y1 := by
  exact AspisR19.R521FamilyObservations.add_opening_of_zero _ g x1 y1
    (family_second_ood_zero t alpha weights x0 y0 x1 y1 circle1)


/-- The joint pair of published OOD openings is preserved by one shared family
correction. Both openings use the same supplied G table and mask weights. -/
theorem family_add_preserves_ood_pair (t : Fin 22 → F) (alpha : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F) (x0 y0 x1 y1 : F)
    (circle0 : x0^2+y0^2=1) (circle1 : x1^2+y1^2=1) :
    let shifted := fun r => g r + AspisR19.R516FiniteGFamily.familyMask
      t alpha (2:F)⁻¹ (x0*y1-y0*x1) (y0-y1) (x1-x0) weights r
    (sourceMaskEvaluate shifted x0 y0, sourceMaskEvaluate shifted x1 y1) =
      (sourceMaskEvaluate g x0 y0, sourceMaskEvaluate g x1 y1) := by
  dsimp only
  exact Prod.ext
    (family_add_preserves_first_ood t alpha weights g x0 y0 x1 y1 circle0)
    (family_add_preserves_second_ood t alpha weights g x0 y0 x1 y1 circle1)

#print axioms family_add_preserves_ood_pair

#print axioms family_first_ood_zero
#print axioms family_second_ood_zero
#print axioms family_add_preserves_first_ood
#print axioms family_add_preserves_second_ood

end AspisR19.R525FamilyOODZero

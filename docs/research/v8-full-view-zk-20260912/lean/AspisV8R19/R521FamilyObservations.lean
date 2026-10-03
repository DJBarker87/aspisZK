import AspisV8R19.R516FiniteGFamily
import AspisR520SourceMaskLinearity.SourceMaskLinearity

set_option autoImplicit false

namespace AspisR19.R521FamilyObservations

open SourceMaskTransport SourceCircleBoundary
open AspisR19.CircleObservationBridge AspisCircleTensorBinding
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem family_root_zero (t : Fin 22 → F) (alpha a b c : F)
    (weights : Fin 13 → F) (rootIndex : Fin 22) (x y : F)
    (circle : x^2 + y^2 = 1)
    (root : doubledFactor x 1 = t rootIndex) :
    sourceMaskEvaluate
      (AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹ a b c weights) x y = 0 := by
  unfold AspisR19.R516FiniteGFamily.familyMask
  rw [AspisR520SourceMaskLinearity.sourceMaskEvaluate_weighted_fin_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [AspisR19.R513SourceDegenerateRoots.selected_mask_root_zero
    t alpha j rootIndex a b c x y circle root]
  simp

theorem family_fibre_zeros (t : Fin 22 → F) (alpha a b c : F)
    (weights : Fin 13 → F) (rootIndex : Fin 22) (x y : F)
    (circle : x^2 + y^2 = 1)
    (root : doubledFactor x 1 = t rootIndex) :
    let m := AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹ a b c weights
    sourceMaskEvaluate m x y = 0 ∧
    sourceMaskEvaluate m x (-y) = 0 ∧
    sourceMaskEvaluate m (-x) (-y) = 0 ∧
    sourceMaskEvaluate m (-x) y = 0 := by
  dsimp only
  exact ⟨family_root_zero t alpha a b c weights rootIndex x y circle root,
    family_root_zero t alpha a b c weights rootIndex x (-y) (by simpa using circle) root,
    family_root_zero t alpha a b c weights rootIndex (-x) (-y)
      (by simpa using circle) (by rwa [doubled_neg]),
    family_root_zero t alpha a b c weights rootIndex (-x) y
      (by simpa using circle) (by rwa [doubled_neg])⟩

omit [NeZero (2 : F)] in
theorem add_opening_of_zero (m g : Fin 1024 → F) (x y : F)
    (h : sourceMaskEvaluate m x y = 0) :
    sourceMaskEvaluate (fun r => g r + m r) x y = sourceMaskEvaluate g x y := by
  change sourceMaskEvaluate (g + m) x y = _
  rw [AspisR520SourceMaskLinearity.sourceMaskEvaluate_add, h, add_zero]

theorem family_add_preserves_root_opening (t : Fin 22 → F) (alpha a b c : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F)
    (rootIndex : Fin 22) (x y : F) (circle : x^2 + y^2 = 1)
    (root : doubledFactor x 1 = t rootIndex) :
    sourceMaskEvaluate
      (fun r => g r + AspisR19.R516FiniteGFamily.familyMask
        t alpha (2:F)⁻¹ a b c weights r) x y = sourceMaskEvaluate g x y := by
  exact add_opening_of_zero _ g x y
    (family_root_zero t alpha a b c weights rootIndex x y circle root)

theorem family_add_preserves_fibre_openings (t : Fin 22 → F) (alpha a b c : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F)
    (rootIndex : Fin 22) (x y : F) (circle : x^2 + y^2 = 1)
    (root : doubledFactor x 1 = t rootIndex) :
    let m := AspisR19.R516FiniteGFamily.familyMask t alpha (2:F)⁻¹ a b c weights
    sourceMaskEvaluate (fun r => g r + m r) x y = sourceMaskEvaluate g x y ∧
    sourceMaskEvaluate (fun r => g r + m r) x (-y) = sourceMaskEvaluate g x (-y) ∧
    sourceMaskEvaluate (fun r => g r + m r) (-x) (-y) = sourceMaskEvaluate g (-x) (-y) ∧
    sourceMaskEvaluate (fun r => g r + m r) (-x) y = sourceMaskEvaluate g (-x) y := by
  dsimp only
  have h := family_fibre_zeros t alpha a b c weights rootIndex x y circle root
  exact ⟨add_opening_of_zero _ g x y h.1,
    add_opening_of_zero _ g x (-y) h.2.1,
    add_opening_of_zero _ g (-x) (-y) h.2.2.1,
    add_opening_of_zero _ g (-x) y h.2.2.2⟩

#print axioms add_opening_of_zero
#print axioms family_root_zero
#print axioms family_fibre_zeros
#print axioms family_add_preserves_root_opening
#print axioms family_add_preserves_fibre_openings

end AspisR19.R521FamilyObservations

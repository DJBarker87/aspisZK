import AspisV8R19.R514DegenerateGCore

set_option autoImplicit false

namespace AspisR19.R516FiniteGFamily

open SourceMaskTransport SourceCircleBoundary
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

def familyMask (t : Fin 22 → F) (alpha half a b c : F)
    (weights : Fin 13 → F) (r : Fin 1024) : F :=
  ∑ j : Fin 13, weights j *
    SourceMaskTransport.mask half a b c (SourceCircleBoundary.column t alpha j) r

theorem family_mask_balanced (t : Fin 22 → F) (alpha half a b c : F)
    (weights : Fin 13 → F) :
    ∑ r ∈ T163SourceTable.inactive,
      familyMask t alpha half a b c weights r = 0 := by
  unfold familyMask
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.mul_sum]
  rw [SourceMaskTransport.mask_balanced]
  simp

theorem family_mask_mixed_coin_zero (t : Fin 22 → F) (alpha half a b c : F)
    (weights : Fin 13 → F) (i : Fin 271) :
    SourceMaskTransport.mixedCoin (familyMask t alpha half a b c weights) i = 0 := by
  unfold familyMask SourceMaskTransport.mixedCoin
  apply Finset.sum_eq_zero
  intro j _
  have h := AspisR19.R514DegenerateGCore.source_mask_coins_zero
    t alpha half a b c j i
  simpa only [SourceMaskTransport.mixedCoin] using h

#print axioms family_mask_balanced
#print axioms family_mask_mixed_coin_zero

end AspisR19.R516FiniteGFamily

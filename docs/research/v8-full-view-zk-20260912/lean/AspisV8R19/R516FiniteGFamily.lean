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

omit [NeZero (2 : F)] in
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
    t half alpha a b c j i
  simp only [SourceMaskTransport.mixedCoin] at h
  rw [h]
  simp

/-- These directions preserve the existing G coordinates for every supplied
G table. Their ability to solve all joint C1/H1/G targets is not asserted. -/
theorem family_preserves_mixed_coins (t : Fin 22 → F) (alpha half a b c : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F) (i : Fin 271) :
    mixedCoin (fun r => g r + familyMask t alpha half a b c weights r) i =
      mixedCoin g i := by
  have hz := family_mask_mixed_coin_zero t alpha half a b c weights i
  change g (T163SourceTable.order (coinIndex i)) +
    mixedCoin (familyMask t alpha half a b c weights) i = mixedCoin g i
  rw [hz, add_zero]
  rfl

omit [NeZero (2 : F)] in
theorem family_preserves_balance (t : Fin 22 → F) (alpha half a b c : F)
    (weights : Fin 13 → F) (g : Fin 1024 → F)
    (hg : ∑ r ∈ T163SourceTable.inactive, g r = 0) :
    ∑ r ∈ T163SourceTable.inactive,
      (g r + familyMask t alpha half a b c weights r) = 0 := by
  rw [Finset.sum_add_distrib, hg, family_mask_balanced, add_zero]

#print axioms family_preserves_mixed_coins
#print axioms family_preserves_balance

#print axioms family_mask_balanced
#print axioms family_mask_mixed_coin_zero

end AspisR19.R516FiniteGFamily

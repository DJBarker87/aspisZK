import AspisV8R19.R645TwoSwapHighDirections
import AspisV8R19.R562ChannelTargetBoundary
set_option autoImplicit false
namespace AspisV8R19.R647TwoSwapStructuredMoment
open AspisV8R17 AspisV8R16 AspisR19
open scoped BigOperators
open R645TwoSwapHighDirections
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Every selected sparse functional vanishes on these source columns under
its actual two-swap routing. Weights, query roots and challenges are arbitrary. -/
theorem actual_sparse_pairing_zero (t : Fin 22 → F) (half alpha a b c : F)
    (j : Fin 13) (weights : Fin 271 → F) :
    (∑ r : Fin 1024, TwoSwapSourceG.original weights r *
      actualMask half a b c (SourceCircleBoundary.column t alpha j) r) = 0 := by
  rw [R561.original_pairing]
  apply Finset.sum_eq_zero
  intro i _
  change weights i * actualCoin (actualMask half a b c
    (SourceCircleBoundary.column t alpha j)) i = 0
  rw [actual_selected_coins_zero, mul_zero]

/-- The structured channel moment requires only the two retained point
conditions for this family: sparse-mask, inactive-balance and both image-tail
conditions follow from the construction. Coverage and those point conditions
are not asserted here. -/
theorem selected_structured_moment_zero (t : Fin 22 → F)
    (half alpha a b c tau kappa : F) (j : Fin 13)
    (points : Fin 3 → Fin 10 → F) (weights : Fin 271 → F)
    (hp1 : sourcePointFunctional (points 1)
      (actualMask half a b c (SourceCircleBoundary.column t alpha j)) = 0)
    (hp2 : sourcePointFunctional (points 2)
      (actualMask half a b c (SourceCircleBoundary.column t alpha j)) = 0) :
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023
        TwoSwapSourceTable.order
        (sourceOriginalWeight points kappa TwoSwapSourceTable.inactive
          (TwoSwapSourceG.original weights) true))) a b c tau true)
      (NormalizedGCore.flatten (SourceCircleBoundary.column t alpha j)) = 0 := by
  apply R562.structured_claim_zero half points kappa TwoSwapSourceTable.inactive
    1023 TwoSwapSourceTable.order (TwoSwapSourceG.original weights)
    (NormalizedGCore.flatten (SourceCircleBoundary.column t alpha j)) a b c tau
  · exact actual_sparse_pairing_zero t half alpha a b c j weights
  · exact hp1
  · exact hp2
  · exact actual_mask_balanced half a b c (SourceCircleBoundary.column t alpha j)
  · exact (SourceMaskBoundary.quotient_image_tail
      (SourceCircleBoundary.column t alpha j) b c).1
  · exact (SourceMaskBoundary.quotient_image_tail
      (SourceCircleBoundary.column t alpha j) b c).2

#print axioms actual_sparse_pairing_zero
#print axioms selected_structured_moment_zero
end
end AspisV8R19.R647TwoSwapStructuredMoment

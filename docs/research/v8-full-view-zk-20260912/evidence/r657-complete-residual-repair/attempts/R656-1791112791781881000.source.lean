import AspisV8R19.R655SourceResidualCompletion
set_option autoImplicit false
namespace AspisV8R19.R656CombinationStructuredMoment
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel
open R653SourceCoefficientBoundary
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- All 271 sparse coins of the exact residual combination vanish, so every
original sparse-mask pairing vanishes, at arbitrary weights. -/
theorem combination_sparse_pairing_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half alpha a b c : F) (x : Fin 13 → F) (weights : Fin 271 → F) :
    (∑ r : Fin 1024, TwoSwapSourceG.original weights r *
      actualMask half a b c (combination t ht noneOne alpha x) r) = 0 := by
  rw [R561.original_pairing]
  apply Finset.sum_eq_zero
  intro i _
  change weights i * actualCoin (actualMask half a b c
    (combination t ht noneOne alpha x)) i = 0
  rw [combination_sparse_coins_zero, mul_zero]

/-- For the exact combination, the two retained point equations imply its
complete structured channel moment. Sparse pairing, balance, and both tails
are derived rather than assumed. Query-table conditions remain explicit. -/
theorem combination_structured_moment_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half alpha a b c kappa tau : F) (x : Fin 13 → F)
    (z : Fin 10 → F) (previous : Fin 271 → F)
    (hp1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (actualMask half a b c (combination t ht noneOne alpha x)) = 0)
    (hp2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (actualMask half a b c (combination t ht noneOne alpha x)) = 0) :
    rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true)
      (NormalizedGCore.flatten (combination t ht noneOne alpha x)) = 0 := by
  unfold TwoSwapResidualSource.quotientWeight TwoSwapResidualSource.originalWeight
  apply R562.structured_claim_zero half (SourceStatementPoints.points z) kappa
    TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (TwoSwapSourceG.original (SourceGConstant.finishCoins half previous))
    (NormalizedGCore.flatten (combination t ht noneOne alpha x)) a b c tau
  · exact combination_sparse_pairing_zero t ht noneOne half alpha a b c x _
  · exact hp1
  · exact hp2
  · exact actual_mask_balanced half a b c (combination t ht noneOne alpha x)
  · exact (SourceMaskBoundary.quotient_image_tail (combination t ht noneOne alpha x) b c).1
  · exact (SourceMaskBoundary.quotient_image_tail (combination t ht noneOne alpha x) b c).2

/-- The exact low-block structured moment needed by coefficient completion
follows from the source channel moment; no target compatibility is assumed. -/
theorem combination_low_structured_moment_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half alpha a b c kappa tau : F) (x : Fin 13 → F)
    (z : Fin 10 → F) (previous : Fin 271 → F)
    (hp1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (actualMask half a b c (combination t ht noneOne alpha x)) = 0)
    (hp2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (actualMask half a b c (combination t ht noneOne alpha x)) = 0) :
    (∑ d : Fin 32, ∑ s : Fin 4, combination t ht noneOne alpha x (d,s) *
      TwoSwapResidualModel.weight half a b c kappa z true (d,s)) = 0 := by
  have hm := combination_structured_moment_zero t ht noneOne half alpha a b c kappa tau x z previous hp1 hp2
  unfold TwoSwapResidualSource.quotientWeight at hm
  rw [source_pairing_low] at hm
  simp only [TwoSwapResidualSource.weight_eq] at hm
  simpa only [Fintype.sum_prod_type] using hm

#print axioms combination_sparse_pairing_zero
#print axioms combination_structured_moment_zero
#print axioms combination_low_structured_moment_zero
end
end AspisV8R19.R656CombinationStructuredMoment

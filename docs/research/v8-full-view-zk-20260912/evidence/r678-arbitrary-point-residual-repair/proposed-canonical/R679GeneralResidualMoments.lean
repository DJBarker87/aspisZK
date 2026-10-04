import AspisV8R19.R670AllPointResidualRepair
set_option autoImplicit false
namespace AspisV8R19.R679GeneralResidualMoments
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R645TwoSwapHighDirections R649TwoSwapResidualRepair R656CombinationStructuredMoment
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
theorem low_plain_moment_general (half a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (q : Index 32 → F)
:
    (∑ d : Fin 32, ∑ s : Fin 4, q (d,s)*TwoSwapResidualModel.weight half a b c kappa z false (d,s)) =
      kappa*sourcePointFunctional (SourceStatementPoints.points z 0) (actualMask half a b c q) +
      kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (actualMask half a b c q) +
      kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (actualMask half a b c q) := by
  have h := original_weights_transported_pairing half (SourceStatementPoints.points z) kappa
    TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (TwoSwapSourceG.original (SourceGConstant.finishCoins half previous))
    (NormalizedGCore.flatten q) a b c tau false
  change rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false)
    (NormalizedGCore.flatten q) =
    (kappa*sourcePointFunctional (SourceStatementPoints.points z 0) (actualMask half a b c q) +
      kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (actualMask half a b c q) +
      kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (actualMask half a b c q) +
      ∑ i ∈ TwoSwapSourceTable.inactive, actualMask half a b c q i) +
      tau*NormalizedGCore.flatten q 1023 +
      tau^2*(b*NormalizedGCore.flatten q 1022-c*NormalizedGCore.flatten q 1021) at h
  rw [actual_mask_balanced,(SourceMaskBoundary.quotient_image_tail q b c).1,
    (SourceMaskBoundary.quotient_image_tail q b c).2] at h
  simp only [mul_zero,add_zero] at h
  unfold TwoSwapResidualSource.quotientWeight at h
  rw [R653SourceCoefficientBoundary.source_pairing_low] at h
  simp only [TwoSwapResidualSource.weight_eq] at h
  simpa only [Fintype.sum_prod_type] using h

theorem combination_low_structured_moment_general (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half alpha a b c kappa tau : F) (x : Fin 13 → F)
    (z : Fin 10 → F) (previous : Fin 271 → F) :
    (∑ d : Fin 32, ∑ s : Fin 4, combination t ht noneOne alpha x (d,s) *
      TwoSwapResidualModel.weight half a b c kappa z true (d,s)) =
      kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1)
        (actualMask half a b c (combination t ht noneOne alpha x)) +
      kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2)
        (actualMask half a b c (combination t ht noneOne alpha x)) := by
  let q := combination t ht noneOne alpha x
  have h := original_weights_transported_pairing half (SourceStatementPoints.points z) kappa
    TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (TwoSwapSourceG.original (SourceGConstant.finishCoins half previous))
    (NormalizedGCore.flatten q) a b c tau true
  change rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true)
    (NormalizedGCore.flatten q) =
    (kappa*(∑ r : Fin 1024, TwoSwapSourceG.original (SourceGConstant.finishCoins half previous) r *
        actualMask half a b c q r) +
      kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (actualMask half a b c q) +
      kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (actualMask half a b c q) +
      ∑ r ∈ TwoSwapSourceTable.inactive, actualMask half a b c q r) +
      tau^3*NormalizedGCore.flatten q 1023 +
      tau^4*(b*NormalizedGCore.flatten q 1022-c*NormalizedGCore.flatten q 1021) at h
  rw [combination_sparse_pairing_zero t ht noneOne half alpha a b c x _,
    actual_mask_balanced,(SourceMaskBoundary.quotient_image_tail q b c).1,
    (SourceMaskBoundary.quotient_image_tail q b c).2] at h
  simp only [mul_zero,add_zero,zero_add] at h
  unfold TwoSwapResidualSource.quotientWeight at h
  rw [R653SourceCoefficientBoundary.source_pairing_low] at h
  simp only [TwoSwapResidualSource.weight_eq] at h
  simpa only [Fintype.sum_prod_type] using h

#print axioms low_plain_moment_general
#print axioms combination_low_structured_moment_general
end
end AspisV8R19.R679GeneralResidualMoments

import AspisV8R19.R650ResidualCombinationKernel
set_option autoImplicit false
namespace AspisV8R19.R651ResidualKernelRepair
open AspisR19 AspisV8R17 HighRepairInvariant
open AspisR19.R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- The exact source-shaped residual system can hit every selected target
while preserving all sparse coins, modeled query evaluations, first folds and
inactive balance. Actual query-root conditions and the nonzero determinant
remain explicit; this is not whole joint-view privacy or a probability law. -/
theorem residual_kernel_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (target : Fin 13 → F)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ i : Fin 13, TwoSwapResidualSource.observed half quarter a b c kappa tau z previous
        (combination t ht noneOne alpha x) (ResidualModel.selectedRow i) = target i) ∧
      (∀ i : Fin 271, actualCoin (actualMask half a b c
        (combination t ht noneOne alpha x)) i = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha
        (combination t ht noneOne alpha x) d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive, actualMask half a b c
        (combination t ht noneOne alpha x) r) = 0 := by
  obtain ⟨x,hx⟩ := selected_residual_repair t ht noneOne half quarter a b c kappa alpha tau z previous target hdet
  exact ⟨x,hx,combination_sparse_coins_zero t ht noneOne half alpha a b c x,
    combination_query_root_zero t ht noneOne alpha x,
    combination_first_fold_zero t ht noneOne alpha x,
    actual_mask_balanced half a b c (combination t ht noneOne alpha x)⟩

#print axioms residual_kernel_repair
end
end AspisV8R19.R651ResidualKernelRepair

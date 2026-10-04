import AspisV8R19.R649TwoSwapResidualRepair

/-! Linear invariants of arbitrary combinations of the exact selected
AugmentedQuotient residual columns. This is field/table algebra only. -/
set_option autoImplicit false
namespace AspisV8R19.R650ResidualCombinationKernel

open AspisV8R17
open AspisR19 AspisR19.HighRepairInvariant AspisR19.NormalizedGCore
open AspisR19.HighQueryGCore AspisR19.TwoSwapWitness
open AspisR19.TwoSwapSourceG
open AspisR19.R645TwoSwapHighDirections
open AspisV8R19.R649TwoSwapResidualRepair
open scoped BigOperators

noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem selected_degree_le_30 (j : Fin 13) :
    (TwoSwapWitness.degree j).val ≤ 30 := by
  fin_cases j <;> decide

private theorem combination_flatten_high (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (alpha : F) (x : Fin 13 → F) (r : Nat) (hr : 124 ≤ r) :
    flatten (combination t ht noneOne alpha x) r = 0 := by
  unfold flatten combination
  by_cases h : r < 128
  · simp only [dif_pos h]
    apply Finset.sum_eq_zero
    intro j _
    rw [mul_eq_zero]
    right
    simp only [AugmentedQuotient.quotient, AugmentedQuotient.lift]
    rw [AugmentedQuerySection.normalized_high t ht noneOne _ _ (by
      change 23 ≤ r / 4
      omega)]
    have hne : (⟨r / 4, by omega⟩ : Fin 32) ≠ TwoSwapWitness.degree j := by
      intro he
      have hv := congrArg Fin.val he
      change r / 4 = (TwoSwapWitness.degree j).val at hv
      have hd := selected_degree_le_30 j
      omega
    simp [hne]
  · simp [h]

theorem combination_sparse_coins_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half alpha a b c : F) (x : Fin 13 → F) (i : Fin 271) :
    actualCoin (actualMask half a b c (combination t ht noneOne alpha x)) i = 0 := by
  rw [actual_mask_coin]
  apply sourceChord_support half _ 62 ?_ a b c _ ?_
  · intro r hr
    exact combination_flatten_high t ht noneOne alpha x r (by omega)
  · change 127 ≤ 128 + 3 * i.val
    omega

theorem combination_query_root_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (alpha : F) (x : Fin 13 → F) (slot : Fin 4) (root : Fin 22) :
    NormalizedQuerySection.evaluate
      (fun d => combination t ht noneOne alpha x (d, slot)) (t root) = 0 := by
  unfold combination NormalizedQuerySection.evaluate
  calc
    (∑ d : Fin 32, (∑ j : Fin 13, x j *
        AugmentedQuotient.quotient t ht noneOne alpha
          (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,slot)) *
        AspisCircleTensorBinding.naturalLineValue (t root) d.val) =
      ∑ d : Fin 32, ∑ j : Fin 13, (x j *
        AugmentedQuotient.quotient t ht noneOne alpha
          (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,slot)) *
        AspisCircleTensorBinding.naturalLineValue (t root) d.val := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_mul]
    _ = ∑ j : Fin 13, x j * ∑ d : Fin 32,
        AugmentedQuotient.quotient t ht noneOne alpha
          (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,slot) *
        AspisCircleTensorBinding.naturalLineValue (t root) d.val := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [show (∑ d : Fin 32,
          AugmentedQuotient.quotient t ht noneOne alpha
            (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,slot) *
          AspisCircleTensorBinding.naturalLineValue (t root) d.val) = 0 from
          AugmentedQuotient.quotient_root t ht noneOne alpha
            (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) slot root,
          mul_zero]

theorem combination_first_fold_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (alpha : F) (x : Fin 13 → F) (d : Fin 32) :
    R370KernelEvaluation.firstFold 32 alpha (combination t ht noneOne alpha x) d = 0 := by
  unfold R370KernelEvaluation.firstFold combination
  calc
    (∑ s : Fin 4, (∑ j : Fin 13, x j *
        AugmentedQuotient.quotient t ht noneOne alpha
          (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,s)) * alpha^s.val) =
      ∑ s : Fin 4, ∑ j : Fin 13, (x j *
        AugmentedQuotient.quotient t ht noneOne alpha
          (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,s)) * alpha^s.val := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_mul]
    _ = ∑ j : Fin 13, x j * ∑ s : Fin 4, alpha^s.val *
        AugmentedQuotient.quotient t ht noneOne alpha
          (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,s) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [AugmentedQuotient.quotient_fold, mul_zero]

#print axioms combination_sparse_coins_zero
#print axioms combination_query_root_zero
#print axioms combination_first_fold_zero

end
end AspisV8R19.R650ResidualCombinationKernel

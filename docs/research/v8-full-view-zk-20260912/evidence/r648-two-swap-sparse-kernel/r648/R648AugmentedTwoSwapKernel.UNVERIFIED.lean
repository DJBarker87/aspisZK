import AspisV8R19.R645TwoSwapHighDirections
import AspisV8R19.TwoSwapSourceWeights

/-! Exact field/table sparse-coin preservation for the selected 13
AugmentedQuotient directions through the TwoSwap routing. The query-root
premises remain explicit; this is not native execution or coverage. -/
set_option autoImplicit false
namespace AspisR19.R648AugmentedTwoSwapKernel

open AspisV8R17
open AspisR19.HighRepairInvariant
open AspisR19.NormalizedGCore
open AspisR19.HighQueryGCore
open AspisR19.TwoSwapWitness
open AspisR19.TwoSwapSourceG
open AspisR19.R645TwoSwapHighDirections

noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem selected_degree_le_30 (j : Fin 13) :
    (TwoSwapWitness.degree j).val ≤ 30 := by
  fin_cases j <;> decide

private theorem flattened_selected_high (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (alpha : F) (j : Fin 13) (r : Nat) (hr : 124 ≤ r) :
    flatten (AugmentedQuotient.quotient t ht noneOne alpha
      (TwoSwapWitness.degree j) (TwoSwapWitness.slot j)) r = 0 := by
  unfold flatten
  by_cases h : r < 128
  · simp only [dif_pos h, AugmentedQuotient.quotient, AugmentedQuotient.lift]
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

theorem actual_selected_coins_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half alpha a b c : F) (j : Fin 13) (i : Fin 271) :
    actualCoin (actualMask half a b c
      (AugmentedQuotient.quotient t ht noneOne alpha
        (TwoSwapWitness.degree j) (TwoSwapWitness.slot j))) i = 0 := by
  rw [actual_mask_coin]
  apply sourceChord_support half _ 62 ?_ a b c _ ?_
  · intro r hr
    exact flattened_selected_high t ht noneOne alpha j r (by omega)
  · change 127 ≤ 128 + 3 * i.val
    omega

omit [NeZero (2 : F)] in
theorem source_weights_mask_eq (half a b c : F) (q : Index 32 → F) :
    TwoSwapSourceWeights.mask half a b c q = actualMask half a b c q := rfl

#print axioms actual_selected_coins_zero
#print axioms source_weights_mask_eq

end
end AspisR19.R648AugmentedTwoSwapKernel

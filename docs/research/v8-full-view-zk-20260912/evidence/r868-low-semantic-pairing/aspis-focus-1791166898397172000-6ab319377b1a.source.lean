import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R662FullIndexedMaskPreservation
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R645TwoSwapHighDirections

/-! Low query-normalization directions preserve every actual sparse coin and
therefore every fixed semantic pairing. -/
set_option autoImplicit false
namespace AspisV8R19.R868LowSemanticPairing
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisR19.R645TwoSwapHighDirections
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R661TwoSwapMaskAddition
open AspisV8R19.R773LowActiveKernel
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Every selected sparse coin reads a source code at least 96, where a low
indexed direction has zero chord value. -/
theorem actual_coin_indexedDirection_zero
    (half alpha a b c : F) (d : Fin 23) (s : Fin 3) (i : Fin 271) :
    actualCoin (indexedMask half a b c
      (indexedDirection alpha (⟨d.val, by omega⟩ : Fin 255) s)) i = 0 := by
  simp only [actualCoin, indexedMask, fullMask, R562.inverseChordMessage,
    inverseTransport, if_neg (TwoSwapSourceG.coin_not_pivot i), Equiv.symm_apply_apply]
  rw [← rawFlatten_eq_flattenFull, rawFlatten_indexedDirection]
  exact sourceChord_low_direction_zero half a b c alpha d s
    (TwoSwapSourceG.coinIndex i).val (by simp only [TwoSwapSourceG.coinIndex]; omega)

/-- Hence the low direction has zero pairing against an arbitrary retained
271-coordinate semantic weight vector. -/
theorem weighted_actual_coin_indexedDirection_zero
    (half alpha a b c : F) (previous : Fin 271 → F) (d : Fin 23) (s : Fin 3) :
    (∑ i : Fin 271, previous i * actualCoin (indexedMask half a b c
      (indexedDirection alpha (⟨d.val, by omega⟩ : Fin 255) s)) i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [actual_coin_indexedDirection_zero]
  ring

#print axioms actual_coin_indexedDirection_zero
#print axioms weighted_actual_coin_indexedDirection_zero
end
end AspisV8R19.R868LowSemanticPairing

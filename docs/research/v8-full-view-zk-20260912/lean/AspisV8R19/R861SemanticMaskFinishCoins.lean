import AspisV8R19.R561SparseGPairing
import AspisV8R19.SourceGConstant
import AspisV8R17.MaskWeightVector
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R861SemanticMaskFinishCoins
open AspisV8R17
open AspisR19.TwoSwapSourceG
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

theorem semantic_mask_first_weight (half : F) (z : RoundCoins F 10) :
    maskWeights271 half z 0 = half^10 := by
  unfold maskWeights271 listAsFin flatMaskWeights
  change (reverseWeightBlocks 26 half 10 z).2 = half^10
  exact reverseWeightBlocks_scale 26 half 10 z

theorem finishCoins_semantic_mask (half : F) (z : RoundCoins F 10) :
    AspisR19.SourceGConstant.finishCoins half (maskWeights271 half z) = maskWeights271 half z := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [AspisR19.SourceGConstant.finishCoins, AspisR19.SourceGConstant.finalScale_eq,
      semantic_mask_first_weight, Function.update]
  · simp [AspisR19.SourceGConstant.finishCoins, AspisR19.SourceGConstant.finalScale_eq,
      Function.update, hi]

theorem semantic_mask_original_pairing (half : F) (z : RoundCoins F 10)
    (m : Fin 1024 → F) :
    (∑ r : Fin 1024,
      AspisR19.TwoSwapSourceG.original (AspisR19.SourceGConstant.finishCoins half (maskWeights271 half z)) r * m r) =
      ∑ i : Fin 271, maskWeights271 half z i * m (AspisR19.TwoSwapSourceTable.order (AspisR19.TwoSwapSourceG.coinIndex i)) := by
  rw [finishCoins_semantic_mask]
  exact R561.original_pairing (maskWeights271 half z) m

#print axioms semantic_mask_first_weight
#print axioms finishCoins_semantic_mask
#print axioms semantic_mask_original_pairing
end
end AspisV8R19.R861SemanticMaskFinishCoins

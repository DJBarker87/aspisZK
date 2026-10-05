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
  simp only [maskWeights271, listAsFin, flatMaskWeights, List.get_cons_zero]
  exact reverseWeightBlocks_scale 26 half 10 z

theorem finishCoins_semantic_mask (half : F) (z : RoundCoins F 10) :
    SourceGConstant.finishCoins half (maskWeights271 half z) = maskWeights271 half z := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [SourceGConstant.finishCoins, SourceGConstant.finalScale_eq,
      Function.update_same, semantic_mask_first_weight]
  · simp only [SourceGConstant.finishCoins, SourceGConstant.finalScale_eq,
      Function.update_of_ne hi]

theorem semantic_mask_original_pairing (half : F) (z : RoundCoins F 10)
    (m : Fin 1024 → F) :
    (∑ r : Fin 1024,
      TwoSwapSourceG.original (SourceGConstant.finishCoins half (maskWeights271 half z)) r * m r) =
      ∑ i : Fin 271, maskWeights271 half z i * m (TwoSwapSourceG.order (TwoSwapSourceG.coinIndex i)) := by
  rw [finishCoins_semantic_mask]
  exact R561.original_pairing (maskWeights271 half z) m

#print axioms semantic_mask_first_weight
#print axioms finishCoins_semantic_mask
#print axioms semantic_mask_original_pairing
end AspisV8R19.R861SemanticMaskFinishCoins
end

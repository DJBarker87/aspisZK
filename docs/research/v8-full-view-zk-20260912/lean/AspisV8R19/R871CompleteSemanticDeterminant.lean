import AspisV8R19.R865PointWeightBlock
import AspisV8R19.R870AugmentedSemanticDeterminant
import AspisV8R19.R872NormalizedAugmentedSemanticMatrix

set_option autoImplicit false
namespace AspisV8R19.R871CompleteSemanticDeterminant
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R864SemanticKernel
open AspisV8R19.R870AugmentedSemanticDeterminant
open AspisV8R19.R872NormalizedAugmentedSemanticMatrix
noncomputable section
local instance : Fact (Nat.Prime 2147483647) := AspisV8R15.ExactTowerBase.m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩

theorem exact_point_blocks : ∀ p : Fin 3, ∀ t : Fin 4,
    pointWeight halfSelected 7 5 (-5) (AspisR19.SourceStatementPoints.points z p) (384+t.val) =
      pointWeight halfSelected 7 5 (-5) (AspisR19.SourceStatementPoints.points z p) t.val := by
  have hz : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
    funext i
    fin_cases i <;> norm_num [z, AspisR19.R750WitnessPointSupport.zFin10]
  intro p t
  simpa only [hz, R865PointWeightBlock.pw, halfSelected, R865PointWeightBlock.half] using
    R865PointWeightBlock.all_three_point_weight_blocks p t

theorem complete_augmented_det_ne_zero : augmented.det ≠ 0 :=
  augmented_det_ne_zero_of_block_eq exact_point_blocks

theorem complete_normalized_augmented_det_ne_zero (t : Fin 22 → M)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (normalizedAugmented t ht noneOne).det ≠ 0 :=
  normalizedAugmented_det_ne_zero_of_block_eq t ht noneOne exact_point_blocks

#print axioms exact_point_blocks
#print axioms complete_augmented_det_ne_zero
#print axioms complete_normalized_augmented_det_ne_zero
end
end AspisV8R19.R871CompleteSemanticDeterminant

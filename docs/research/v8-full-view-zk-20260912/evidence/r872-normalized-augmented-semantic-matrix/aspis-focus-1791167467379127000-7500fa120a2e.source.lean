import AspisV8R19.R870AugmentedSemanticDeterminant
import AspisV8R19.R869NormalizedSemanticCoins
import AspisV8R19.R784FixedJointNormalization

/-! The fixed selected augmented semantic matrix is unchanged by legal query
normalization.  This is source-field matrix algebra only. -/
set_option autoImplicit false
namespace AspisV8R19.R872NormalizedAugmentedSemanticMatrix
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisR19.R645TwoSwapHighDirections
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R661TwoSwapMaskAddition
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R784FixedJointNormalization
open AspisV8R19.R864SemanticKernel
open AspisV8R19.R869NormalizedSemanticCoins
open AspisV8R19.R870AugmentedSemanticDeterminant
open scoped BigOperators
noncomputable section
local instance : Fact (Nat.Prime 2147483647) := AspisV8R15.ExactTowerBase.m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩

abbrev Obs := R870AugmentedSemanticDeterminant.Obs

def normalizedAugmented (t : Fin 22 → M) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) : Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) M :=
  Matrix.fromBlocks
    (fun r c => rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
      (normalizedPair 7 t ht noneOne (cast255 (selectedColumns c).1)
        (selectedColumns c).2) r)
    (fun r (_ : Unit) => rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
      (normalizedPair 7 t ht noneOne (cast255 96) 0) r)
    (fun (_ : Unit) c => ∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
      actualCoin (indexedMask halfSelected 7 5 (-5)
        (normalizedPair 7 t ht noneOne (cast255 (selectedColumns c).1)
          (selectedColumns c).2)) i)
    (fun (_ : Unit) (_ : Unit) => ∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
      actualCoin (indexedMask halfSelected 7 5 (-5)
        (normalizedPair 7 t ht noneOne (cast255 96) 0)) i)

lemma semantic_eq_actualCoin_pairing (q : R738JointObservationModel.Index256 → M) :
    semantic q = ∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
      actualCoin (indexedMask halfSelected 7 5 (-5) q) i := by
  unfold semantic
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [rawFlatten_eq_flattenFull]
  symm
  simp only [actualCoin, indexedMask, R661TwoSwapMaskAddition.fullMask,
    R562.inverseChordMessage, inverseTransport,
    if_neg (TwoSwapSourceG.coin_not_pivot i), Equiv.symm_apply_apply]
  rfl

/-- All selected and extra source directions retain their exact augmented
matrix entries after the specified 22-root normalization. -/
theorem normalizedAugmented_eq_augmented (t : Fin 22 → M) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    normalizedAugmented t ht noneOne = augmented := by
  unfold normalizedAugmented augmented
  ext row col
  rcases row with r | u <;> rcases col with c | v
  · change rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
      (normalizedPair 7 t ht noneOne (cast255 (selectedColumns c).1)
        (selectedColumns c).2) r =
      rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
        (indexedDirection 7 (selectedColumns c).1 (selectedColumns c).2) r
    rw [← rawObservation_indexedDirection]
    simpa [halfSelected, R779FixedPoint1LowKernel.half,
      R864SemanticKernel.z, R748JointWitnessPointEntry.z] using
      fixed_normalized_observation t ht noneOne (selectedColumns c).1
        (selectedColumns c).2 r
  · change rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
      (normalizedPair 7 t ht noneOne (cast255 96) 0) r =
      rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
        (indexedDirection 7 96 0) r
    rw [← rawObservation_indexedDirection]
    simpa [halfSelected, R779FixedPoint1LowKernel.half,
      R864SemanticKernel.z, R748JointWitnessPointEntry.z] using
      fixed_normalized_observation t ht noneOne (96 : Fin 255) (0 : Fin 3) r
  · change (∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
      actualCoin (indexedMask halfSelected 7 5 (-5)
        (normalizedPair 7 t ht noneOne (cast255 (selectedColumns c).1)
          (selectedColumns c).2)) i) =
      semantic (indexedDirection 7 (selectedColumns c).1 (selectedColumns c).2)
    rw [weighted_actualCoin_normalizedPair, ← semantic_eq_actualCoin_pairing]
  · change (∑ i : Fin 271, maskWeights271 halfSelected semanticZ i *
      actualCoin (indexedMask halfSelected 7 5 (-5)
        (normalizedPair 7 t ht noneOne (cast255 96) 0)) i) =
      semantic (indexedDirection 7 96 0)
    rw [weighted_actualCoin_normalizedPair, ← semantic_eq_actualCoin_pairing]

/-- The existing determinant certificate transfers only under its explicit
point-row hypothesis. -/
theorem normalizedAugmented_det_ne_zero_of_block_eq (t : Fin 22 → M)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (hpoints : ∀ p : Fin 3, ∀ r : Fin 4,
      pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) (384+r.val) =
        pointWeight halfSelected 7 5 (-5) (SourceStatementPoints.points z p) r.val) :
    (normalizedAugmented t ht noneOne).det ≠ 0 := by
  rw [normalizedAugmented_eq_augmented]
  exact augmented_det_ne_zero_of_block_eq hpoints

#print axioms semantic_eq_actualCoin_pairing
#print axioms normalizedAugmented_eq_augmented
#print axioms normalizedAugmented_det_ne_zero_of_block_eq
end
end AspisV8R19.R872NormalizedAugmentedSemanticMatrix

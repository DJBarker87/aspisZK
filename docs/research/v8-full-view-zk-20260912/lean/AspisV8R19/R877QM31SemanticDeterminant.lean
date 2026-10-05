import AspisV8R19.R875AugmentedSemanticMatrixHom
import AspisV8R19.R871CompleteSemanticDeterminant
import AspisV8R19.R791QM31JointNormalization

/-! Fixed-witness source-matrix determinant transfer from the exact M31 model
into QM31.  This is field-model algebra only. -/
set_option autoImplicit false
namespace AspisV8R19.R877QM31SemanticDeterminant
open AspisV8R15.ExactTowerBase
open AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R864SemanticKernel
open AspisV8R19.R870AugmentedSemanticDeterminant
open AspisV8R19.R871CompleteSemanticDeterminant
open AspisV8R19.R872NormalizedAugmentedSemanticMatrix
open AspisV8R19.R875AugmentedSemanticMatrixHom
open AspisV8R19.R873SemanticMaskWeightHom
open AspisV8R19.R791QM31JointNormalization
noncomputable section

local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

abbrev Obs := R870AugmentedSemanticDeterminant.Obs

/-- The generic source-defined matrix is exactly the certified fixed M31
matrix at the selected fixed witness. -/
theorem m31_augmentedMatrix_eq_augmented :
    augmentedMatrix halfSelected (536870912 : M) 7 2 3 5 0 z semanticZ = augmented := by
  unfold augmentedMatrix augmented
  have ha : (1 + (2 : M) * 3) = 7 := by decide
  have hb : ((2 : M) * 3 - 1) = 5 := by decide
  have hc : (-((2 : M) + 3)) = (-5 : M) := by decide
  have hA :
      chosenSourceMatrix halfSelected (536870912 : M) 7 2 3 5 0 z =
        chosenSourceMatrix halfSelected 536870912 7 2 3 5 0 z := rfl
  have htop :
      (fun r (_ : Unit) => rawObservation halfSelected (536870912 : M)
        (1 + (2 : M) * 3) ((2 : M) * 3 - 1) (-((2 : M) + 3)) 5 0 z
        (indexedDirection 7 96 0) r) =
      (fun r (_ : Unit) => rawObservation halfSelected 536870912 7 5 (-5) 5 0 z
        extra r) := by
    funext r u
    rw [ha, hb, hc]
    rfl
  have hbottom :
      (fun (_ : Unit) c => semanticEntry halfSelected (1 + (2 : M) * 3)
        ((2 : M) * 3 - 1) (-((2 : M) + 3)) semanticZ
        (indexedDirection 7 (selectedColumns c).1 (selectedColumns c).2)) =
      (fun (_ : Unit) c => semantic
        (indexedDirection 7 (selectedColumns c).1 (selectedColumns c).2)) := by
    funext u c
    rw [ha, hb, hc]
    unfold semanticEntry
    exact (semantic_eq_actualCoin_pairing _).symm
  have hdelta :
      (fun (_ : Unit) (_ : Unit) => semanticEntry halfSelected (1 + (2 : M) * 3)
        ((2 : M) * 3 - 1) (-((2 : M) + 3)) semanticZ
        (indexedDirection 7 96 0)) =
      (fun (_ : Unit) (_ : Unit) => semantic extra) := by
    funext u v
    rw [ha, hb, hc]
    unfold semanticEntry
    exact (semantic_eq_actualCoin_pairing _).symm
  rw [hA, htop, hbottom, hdelta]

theorem m31_augmentedMatrix_det_ne_zero :
    (augmentedMatrix halfSelected (536870912 : M) 7 2 3 5 0 z semanticZ).det ≠ 0 := by
  rw [m31_augmentedMatrix_eq_augmented]
  exact complete_augmented_det_ne_zero

/-- The same raw source-model matrix over QM31 under the concrete M31 witness
embedding. -/
def qm31Augmented : Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) QM31Exact :=
  augmentedMatrix
    (witnessEmbedding halfSelected)
    (witnessEmbedding (536870912 : M))
    (witnessEmbedding (7 : M))
    (witnessEmbedding (2 : M))
    (witnessEmbedding (3 : M))
    (witnessEmbedding (5 : M))
    (witnessEmbedding (0 : M))
    (fun i => witnessEmbedding (z i))
    (mapCoins witnessEmbedding 10 semanticZ)

theorem qm31Augmented_det_ne_zero : qm31Augmented.det ≠ 0 := by
  intro hzero
  apply m31_augmentedMatrix_det_ne_zero
  apply witnessEmbedding.injective
  rw [map_augmentedMatrix_det]
  exact hzero

#print axioms m31_augmentedMatrix_eq_augmented
#print axioms m31_augmentedMatrix_det_ne_zero
#print axioms qm31Augmented_det_ne_zero
end
end AspisV8R19.R877QM31SemanticDeterminant

import AspisV8R19.R877QM31SemanticDeterminant
import AspisV8R19.R869NormalizedSemanticCoins
import AspisV8R19.R791QM31JointNormalization

/-! Arbitrary 22-root normalization for the fixed QM31 223-entry source matrix. -/
set_option autoImplicit false
namespace AspisV8R19.R879QM31Full223Normalization
open AspisV8R15.ExactTowerBase
open AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R789MappedJointNormalization
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R791QM31JointNormalization
open AspisV8R19.R869NormalizedSemanticCoins
open AspisV8R19.R873SemanticMaskWeightHom
open AspisV8R19.R875AugmentedSemanticMatrixHom
open AspisV8R19.R877QM31SemanticDeterminant
open AspisV8R19.R864SemanticKernel
open AspisR19.R645TwoSwapHighDirections
noncomputable section

local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

abbrev Obs := R877QM31SemanticDeterminant.Obs

/-- The entire raw 223-entry fixed source matrix after legal 22-root
normalization, including its retained 271-coin semantic row. -/
def normalized223 (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) : Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) QM31Exact :=
  Matrix.fromBlocks
    (fun r c => rawObservation
      (witnessEmbedding halfSelected) (witnessEmbedding (536870912 : M))
      (witnessEmbedding (7 : M)) (witnessEmbedding (5 : M))
      (witnessEmbedding (-5 : M)) (witnessEmbedding (5 : M))
      (witnessEmbedding (0 : M)) (fun i => witnessEmbedding (z i))
      (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne
        (cast255 (selectedColumns c).1) (selectedColumns c).2) r)
    (fun r (_ : Unit) => rawObservation
      (witnessEmbedding halfSelected) (witnessEmbedding (536870912 : M))
      (witnessEmbedding (7 : M)) (witnessEmbedding (5 : M))
      (witnessEmbedding (-5 : M)) (witnessEmbedding (5 : M))
      (witnessEmbedding (0 : M)) (fun i => witnessEmbedding (z i))
      (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne (cast255 96) 0) r)
    (fun (_ : Unit) c => ∑ i : Fin 271,
      maskWeights271 (witnessEmbedding halfSelected) (mapCoins witnessEmbedding 10 semanticZ) i *
      actualCoin (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask
        (witnessEmbedding halfSelected) (witnessEmbedding (7 : M))
        (witnessEmbedding (5 : M)) (witnessEmbedding (-5 : M))
        (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne
          (cast255 (selectedColumns c).1) (selectedColumns c).2)) i)
    (fun (_ : Unit) (_ : Unit) => ∑ i : Fin 271,
      maskWeights271 (witnessEmbedding halfSelected) (mapCoins witnessEmbedding 10 semanticZ) i *
      actualCoin (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask
        (witnessEmbedding halfSelected) (witnessEmbedding (7 : M))
        (witnessEmbedding (5 : M)) (witnessEmbedding (-5 : M))
        (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne (cast255 96) 0)) i)

/-- Every normalized block is exactly the fixed embedded raw source block. -/
theorem normalized223_eq_qm31Augmented (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    normalized223 t ht noneOne = qm31Augmented := by
  unfold normalized223 qm31Augmented augmentedMatrix
  have hhalf : halfSelected = AspisV8R19.R779FixedPoint1LowKernel.half := by decide
  have hz : z = AspisV8R19.R748JointWitnessPointEntry.z := by rfl
  have ha : (1 + (2 : QM31Exact) * 3) = 7 := by ring
  have hb : ((2 : QM31Exact) * 3 - 1) = 5 := by ring
  have hc : (-((2 : QM31Exact) + 3)) = (-5 : QM31Exact) := by ring
  have hA :
      (fun r c => rawObservation
        (witnessEmbedding halfSelected) (witnessEmbedding (536870912 : M))
        (witnessEmbedding (7 : M)) (witnessEmbedding (5 : M))
        (witnessEmbedding (-5 : M)) (witnessEmbedding (5 : M))
        (witnessEmbedding (0 : M)) (fun i => witnessEmbedding (z i))
        (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne
          (cast255 (selectedColumns c).1) (selectedColumns c).2) r) =
      chosenSourceMatrix (witnessEmbedding halfSelected)
        (witnessEmbedding (536870912 : M)) (witnessEmbedding (7 : M))
        (witnessEmbedding (2 : M)) (witnessEmbedding (3 : M))
        (witnessEmbedding (5 : M)) (witnessEmbedding (0 : M))
        (fun i => witnessEmbedding (z i)) := by
    change normalizedSelectedMatrix (witnessEmbedding halfSelected)
      (witnessEmbedding (536870912 : M)) (witnessEmbedding (7 : M))
      (witnessEmbedding (2 : M)) (witnessEmbedding (3 : M))
      (witnessEmbedding (5 : M)) (witnessEmbedding (0 : M))
      (fun i => witnessEmbedding (z i)) t ht noneOne = _
    simpa only [hhalf, hz, map_ofNat, map_zero] using qm31_normalized_matrix t ht noneOne
  have htop :
      (fun r (_ : Unit) => rawObservation
        (witnessEmbedding halfSelected) (witnessEmbedding (536870912 : M))
        (witnessEmbedding (7 : M)) (witnessEmbedding (5 : M))
        (witnessEmbedding (-5 : M)) (witnessEmbedding (5 : M))
        (witnessEmbedding (0 : M)) (fun i => witnessEmbedding (z i))
        (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne (cast255 96) 0) r) =
      (fun r (_ : Unit) => rawObservation
        (witnessEmbedding halfSelected) (witnessEmbedding (536870912 : M))
        (witnessEmbedding (1 + (2 : M) * 3))
        (witnessEmbedding ((2 : M) * 3 - 1))
        (witnessEmbedding (-((2 : M) + 3)))
        (witnessEmbedding (5 : M)) (witnessEmbedding (0 : M))
        (fun i => witnessEmbedding (z i))
        (indexedDirection (witnessEmbedding (7 : M)) 96 0) r) := by
    funext r u
    calc
      _ = sparseObservation (witnessEmbedding halfSelected)
          (witnessEmbedding (536870912 : M)) 7 5 (-5) 5 0 7
          (fun i => witnessEmbedding (z i)) (96 : Fin 255) 0 r := by
        simpa only [hhalf, hz, map_ofNat, map_neg, map_zero] using
          (mapped_normalized_observation witnessEmbedding t ht noneOne (96 : Fin 255) (0 : Fin 3) r)
      _ = rawObservation (witnessEmbedding halfSelected) (witnessEmbedding (536870912 : M))
          7 5 (-5) 5 0 (fun i => witnessEmbedding (z i))
          (indexedDirection 7 96 0) r := by
        symm
        symm
        exact rawObservation_indexedDirection _ _ _ _ _ _ _ _ _ _ _
      _ = _ := by simp only [map_one, map_mul, map_sub, map_neg, map_add, map_zero, ha, hb, hc, map_ofNat]
  have hbottom :
      (fun (_ : Unit) c => ∑ i : Fin 271,
        maskWeights271 (witnessEmbedding halfSelected) (mapCoins witnessEmbedding 10 semanticZ) i *
        actualCoin (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask
          (witnessEmbedding halfSelected) (witnessEmbedding (7 : M))
          (witnessEmbedding (5 : M)) (witnessEmbedding (-5 : M))
          (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne
            (cast255 (selectedColumns c).1) (selectedColumns c).2)) i) =
      (fun (_ : Unit) c => semanticEntry
        (witnessEmbedding halfSelected) (witnessEmbedding (1 + (2 : M) * 3))
        (witnessEmbedding ((2 : M) * 3 - 1)) (witnessEmbedding (-((2 : M) + 3)))
        (mapCoins witnessEmbedding 10 semanticZ)
        (indexedDirection (witnessEmbedding (7 : M))
          (selectedColumns c).1 (selectedColumns c).2)) := by
    funext u c
    rw [weighted_actualCoin_normalizedPair]
    simp only [map_one, map_mul, map_sub, map_neg, map_add, map_zero, ha, hb, hc, map_ofNat]
    rfl
  have hdelta :
      (fun (_ : Unit) (_ : Unit) => ∑ i : Fin 271,
        maskWeights271 (witnessEmbedding halfSelected) (mapCoins witnessEmbedding 10 semanticZ) i *
        actualCoin (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask
          (witnessEmbedding halfSelected) (witnessEmbedding (7 : M))
          (witnessEmbedding (5 : M)) (witnessEmbedding (-5 : M))
          (normalizedPair (witnessEmbedding (7 : M)) t ht noneOne (cast255 96) 0)) i) =
      (fun (_ : Unit) (_ : Unit) => semanticEntry
        (witnessEmbedding halfSelected) (witnessEmbedding (1 + (2 : M) * 3))
        (witnessEmbedding ((2 : M) * 3 - 1)) (witnessEmbedding (-((2 : M) + 3)))
        (mapCoins witnessEmbedding 10 semanticZ)
        (indexedDirection (witnessEmbedding (7 : M)) 96 0)) := by
    funext u v
    rw [weighted_actualCoin_normalizedPair]
    simp only [map_one, map_mul, map_sub, map_neg, map_add, map_zero, ha, hb, hc, map_ofNat]
    rfl
  rw [hA, htop, hbottom, hdelta]
  simp only [map_one, map_mul, map_sub, map_neg, map_add, map_zero, map_ofNat]

theorem normalized223_det_ne_zero (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (normalized223 t ht noneOne).det ≠ 0 := by
  rw [normalized223_eq_qm31Augmented]
  exact qm31Augmented_det_ne_zero

#print axioms normalized223_eq_qm31Augmented
#print axioms normalized223_det_ne_zero
end
end AspisV8R19.R879QM31Full223Normalization

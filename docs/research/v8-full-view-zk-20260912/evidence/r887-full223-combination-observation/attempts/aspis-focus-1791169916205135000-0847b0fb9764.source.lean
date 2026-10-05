import AspisV8R19.R882RootFixedAugmentedPolynomial
import AspisV8R19.R764RawJointWeights
import AspisV8R19.R869NormalizedSemanticCoins

set_option autoImplicit false
namespace AspisV8R19.R887Full223CombinationObservation
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R764RawJointWeights
open AspisV8R19.R869NormalizedSemanticCoins
open AspisV8R19.R882RootFixedAugmentedPolynomial
open AspisV8R19.R875AugmentedSemanticMatrixHom
open AspisR19.R645TwoSwapHighDirections
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev Obs := R875AugmentedSemanticMatrixHom.Obs

def augmentedDirection (alpha : F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (col : Obs ⊕ Unit) : R738JointObservationModel.Index256 → F :=
  match col with
  | .inl c => normalizedPair alpha t ht noneOne (cast255 (selectedColumns c).1) (selectedColumns c).2
  | .inr _ => normalizedPair alpha t ht noneOne (cast255 96) 0

def combination223 (alpha : F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (x : Obs ⊕ Unit → F) : R738JointObservationModel.Index256 → F :=
  fun i => ∑ col, x col * augmentedDirection alpha t ht noneOne col i

lemma actualCoin_combination223 (half a b c alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) (coin : Fin 271) :
    actualCoin (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half a b c
      (combination223 alpha t ht noneOne x)) coin =
      ∑ col, x col * actualCoin (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half a b c
        (augmentedDirection alpha t ht noneOne col)) coin := by
  rw [actualCoin_contraction]
  unfold combination223
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ d : Fin 256, ∑ col : Obs ⊕ Unit, ∑ s : Fin 4,
        x col * augmentedDirection alpha t ht noneOne col (d, s) *
          coinWeight half a b c coin (d, s) := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ col : Obs ⊕ Unit, ∑ d : Fin 256, ∑ s : Fin 4,
        x col * augmentedDirection alpha t ht noneOne col (d, s) *
          coinWeight half a b c coin (d, s) := by
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro col _
      rw [← actualCoin_contraction]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem combination223_observation (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) (row : Obs ⊕ Unit) :
    (match row with
    | .inl r => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (combination223 alpha t ht noneOne x) r
    | .inr _ => ∑ i : Fin 271, maskWeights271 half coins i * actualCoin
        (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half (1+u*v) (u*v-1) (-(u+v))
          (combination223 alpha t ht noneOne x)) i) =
    (normalizedSource223 half quarter alpha u v kappa tau z coins t ht noneOne).mulVec x row := by
  rcases row with r | unit
  · rw [rawObservation_weighted]
    unfold combination223
    simp_rw [Finset.sum_mul]
    calc
      _ = ∑ d : Fin 256, ∑ col : Obs ⊕ Unit, ∑ s : Fin 4,
          x col * augmentedDirection alpha t ht noneOne col (d, s) *
            jointWeight half quarter (1 + u * v) (u * v - 1) (-(u + v))
              kappa tau z r (d, s) := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = ∑ col : Obs ⊕ Unit, ∑ d : Fin 256, ∑ s : Fin 4,
          x col * augmentedDirection alpha t ht noneOne col (d, s) *
            jointWeight half quarter (1 + u * v) (u * v - 1) (-(u + v))
              kappa tau z r (d, s) := by
        exact Finset.sum_comm
      _ = _ := by
        unfold normalizedSource223 Matrix.mulVec dotProduct augmentedDirection
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
        apply Finset.sum_congr rfl
        intro col _
        rcases col with c | unit <;> rfl
  · rw [actualCoin_combination223]
    calc
      _ = ∑ col : Obs ⊕ Unit, x col *
          (∑ i : Fin 271, maskWeights271 half coins i * actualCoin
            (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half
              (1 + u * v) (u * v - 1) (-(u + v))
              (augmentedDirection alpha t ht noneOne col)) i) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro col _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        unfold normalizedSource223 Matrix.mulVec dotProduct augmentedDirection
        simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
        apply Finset.sum_congr rfl
        intro col _
        rcases col with c | unit <;> rfl

theorem combination223_surjective (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (hdet : (normalizedSource223 half quarter alpha u v kappa tau z coins t ht noneOne).det ≠ 0)
    (target : Obs ⊕ Unit → F) :
    ∃ x : Obs ⊕ Unit → F, ∀ row,
      (match row with
      | .inl r => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
          (combination223 alpha t ht noneOne x) r
      | .inr _ => ∑ i : Fin 271, maskWeights271 half coins i * actualCoin
          (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half (1+u*v) (u*v-1) (-(u+v))
            (combination223 alpha t ht noneOne x)) i) = target row := by
  have hu : IsUnit (normalizedSource223 half quarter alpha u v kappa tau z coins t ht noneOne) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) target
  refine ⟨x, ?_⟩
  intro row
  rw [combination223_observation]
  exact congrFun hx row

#print axioms actualCoin_combination223
#print axioms combination223_observation
#print axioms combination223_surjective
end
end AspisV8R19.R887Full223CombinationObservation

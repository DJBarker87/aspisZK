import AspisV8R19.R880AugmentedSemanticPolynomial
import AspisV8R19.R833RootFixedJointPolynomial
import AspisV8R19.R834NormalizedJointDegree

/-! Root-fixed polynomial model for all 223 normalized source observations. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R882RootFixedAugmentedPolynomial
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R833RootFixedJointPolynomial
open AspisV8R19.R834NormalizedJointDegree
open AspisV8R19.R843CompleteJointDegree
open AspisV8R19.R869NormalizedSemanticCoins
open AspisV8R19.R880AugmentedSemanticPolynomial
open AspisV8R19.R875AugmentedSemanticMatrixHom
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev Obs := R875AugmentedSemanticMatrixHom.Obs

def normalizedEntry (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 255) (s : Fin 3) (row : Obs) : JointPoly F :=
  polynomialEntry half quarter d s row -
    ∑ j : Fin 23, C (low t ht noneOne (cast255 d) j) *
      polynomialEntry half quarter (⟨j.val, by omega⟩ : Fin 255) s row

theorem eval_normalizedEntry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 255) (s : Fin 3) (row : Obs) :
    eval (assignment alpha u v kappa tau z)
      (normalizedEntry half quarter t ht noneOne d s row) =
    rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
      (normalizedPair alpha t ht noneOne (cast255 d) s) row := by
  unfold normalizedEntry
  rw [map_sub, map_sum]
  simp only [eval_C, map_mul]
  rw [eval_polynomialEntry]
  simp_rw [eval_polynomialEntry]
  rw [rawObservation_indexedDirection]
  simp_rw [rawObservation_indexedDirection]
  exact (normalized_sparse_entry half quarter (1+u*v) (u*v-1) (-(u+v))
    kappa tau alpha z row t ht noneOne d s).symm

def normalizedSource223 (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) F :=
  Matrix.fromBlocks
    (fun r c => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
      (normalizedPair alpha t ht noneOne (cast255 (selectedColumns c).1) (selectedColumns c).2) r)
    (fun r (_ : Unit) => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
      (normalizedPair alpha t ht noneOne (cast255 96) 0) r)
    (fun (_ : Unit) c => ∑ i : Fin 271, maskWeights271 half coins i *
      AspisR19.R645TwoSwapHighDirections.actualCoin
        (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half
          (1+u*v) (u*v-1) (-(u+v))
          (normalizedPair alpha t ht noneOne
            (cast255 (selectedColumns c).1) (selectedColumns c).2)) i)
    (fun (_ : Unit) (_ : Unit) => ∑ i : Fin 271, maskWeights271 half coins i *
      AspisR19.R645TwoSwapHighDirections.actualCoin
        (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half
          (1+u*v) (u*v-1) (-(u+v))
          (normalizedPair alpha t ht noneOne (cast255 96) 0)) i)

def rootFixedAugmentedPolynomial (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (weights : Fin 271 → JointPoly F) :
    Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) (JointPoly F) :=
  Matrix.fromBlocks
    (rootFixedMatrix half quarter t ht noneOne)
    (fun r (_ : Unit) => normalizedEntry half quarter t ht noneOne 96 0 r)
    (fun (_ : Unit) c => semanticPolynomial half weights (selectedColumns c).1 (selectedColumns c).2)
    (fun (_ : Unit) (_ : Unit) => semanticPolynomial half weights 96 0)

theorem eval_rootFixedAugmentedPolynomial (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (weights : Fin 271 → JointPoly F)
    (hw : ∀ i, eval (assignment alpha u v kappa tau z) (weights i) = maskWeights271 half coins i) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix
      (rootFixedAugmentedPolynomial half quarter t ht noneOne weights) =
    normalizedSource223 half quarter alpha u v kappa tau z coins t ht noneOne := by
  unfold rootFixedAugmentedPolynomial normalizedSource223
  have hA := eval_rootFixedMatrix half quarter alpha u v kappa tau z t ht noneOne
  have htop :
      (fun r (_ : Unit) => eval (assignment alpha u v kappa tau z)
        (normalizedEntry half quarter t ht noneOne 96 0 r)) =
      (fun r (_ : Unit) => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (normalizedPair alpha t ht noneOne (cast255 96) 0) r) := by
    funext r unit
    exact eval_normalizedEntry half quarter alpha u v kappa tau z t ht noneOne 96 0 r
  have hs (d : Fin 255) (s : Fin 3) :
      eval (assignment alpha u v kappa tau z) (semanticPolynomial half weights d s) =
      ∑ i : Fin 271, maskWeights271 half coins i *
        AspisR19.R645TwoSwapHighDirections.actualCoin
          (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half
            (1+u*v) (u*v-1) (-(u+v)) (normalizedPair alpha t ht noneOne (cast255 d) s)) i := by
    rw [eval_semanticPolynomial]
    simp_rw [hw]
    exact (weighted_actualCoin_normalizedPair half alpha (1+u*v) (u*v-1) (-(u+v))
      (maskWeights271 half coins) t ht noneOne d s).symm
  have hbottom :
      (fun (_ : Unit) c => eval (assignment alpha u v kappa tau z)
        (semanticPolynomial half weights (selectedColumns c).1 (selectedColumns c).2)) =
      (fun (_ : Unit) c => ∑ i : Fin 271, maskWeights271 half coins i *
        AspisR19.R645TwoSwapHighDirections.actualCoin
          (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half
            (1+u*v) (u*v-1) (-(u+v))
            (normalizedPair alpha t ht noneOne
              (cast255 (selectedColumns c).1) (selectedColumns c).2)) i) := by
    funext unit c
    exact hs (selectedColumns c).1 (selectedColumns c).2
  have hdelta :
      (fun (_ : Unit) (_ : Unit) => eval (assignment alpha u v kappa tau z)
        (semanticPolynomial half weights 96 0)) =
      (fun (_ : Unit) (_ : Unit) => ∑ i : Fin 271, maskWeights271 half coins i *
        AspisR19.R645TwoSwapHighDirections.actualCoin
          (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half
            (1+u*v) (u*v-1) (-(u+v))
            (normalizedPair alpha t ht noneOne (cast255 96) 0)) i) := by
    funext unit unit'
    exact hs 96 0
  rw [hA, htop, hbottom, hdelta]

lemma normalizedEntry_totalDegree_le (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (D : Nat)
    (hraw : ∀ (d : Fin 255) (s : Fin 3) (row : Obs),
      (polynomialEntry half quarter d s row).totalDegree ≤ D)
    (d : Fin 255) (s : Fin 3) (row : Obs) :
    (normalizedEntry half quarter t ht noneOne d s row).totalDegree ≤ D := by
  unfold normalizedEntry
  have hcorrection :
      (∑ j : Fin 23, C (low t ht noneOne (cast255 d) j) *
        polynomialEntry half quarter (⟨j.val, by omega⟩ : Fin 255) s row).totalDegree ≤ D := by
    apply totalDegree_finsetSum_le
    intro j hj
    have hcoeff : (C (low t ht noneOne (cast255 d) j) : JointPoly F).totalDegree ≤ 0 := by simp
    exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add hcoeff
      (hraw (⟨j.val, by omega⟩ : Fin 255) s row))
  exact (totalDegree_sub _ _).trans (max_le (hraw d s row) hcorrection)

theorem rootFixedAugmentedPolynomial_entry_degree (half quarter : F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (weights : Fin 271 → JointPoly F) (hw : ∀ i, (weights i).totalDegree ≤ 27)
    (r c : Obs ⊕ Unit) :
    (rootFixedAugmentedPolynomial half quarter t ht noneOne weights r c).totalDegree ≤ 63 := by
  rcases r with r | unit <;> rcases c with c | unit
  · exact rootFixedMatrix_entry_totalDegree_le half quarter t ht noneOne 63
      (raw_entry_degree half quarter) r c
  · exact normalizedEntry_totalDegree_le half quarter t ht noneOne 63
      (raw_entry_degree half quarter) 96 0 r
  · exact (semanticPolynomial_degree half weights hw _ _).trans (by decide)
  · exact (semanticPolynomial_degree half weights hw 96 0).trans (by decide)

theorem rootFixedAugmentedPolynomial_det_degree (half quarter : F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (weights : Fin 271 → JointPoly F) (hw : ∀ i, (weights i).totalDegree ≤ 27) :
    (rootFixedAugmentedPolynomial half quarter t ht noneOne weights).det.totalDegree ≤ 14049 := by
  have h := AspisV8R17.minor_totalDegree
    (rootFixedAugmentedPolynomial half quarter t ht noneOne weights) 63
    (rootFixedAugmentedPolynomial_entry_degree half quarter t ht noneOne weights hw)
  have hc : Fintype.card (Obs ⊕ Unit) = 223 := by
    rw [Fintype.card_sum, observation_card, Fintype.card_unique]
  rw [hc] at h
  exact h

#print axioms eval_normalizedEntry
#print axioms eval_rootFixedAugmentedPolynomial
#print axioms normalizedEntry_totalDegree_le
#print axioms rootFixedAugmentedPolynomial_entry_degree
#print axioms rootFixedAugmentedPolynomial_det_degree
end
end AspisV8R19.R882RootFixedAugmentedPolynomial

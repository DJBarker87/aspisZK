import AspisV8R19.R878SemanticChordPolynomial
import AspisV8R19.R875AugmentedSemanticMatrixHom
import AspisV8R19.R843CompleteJointDegree

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R880AugmentedSemanticPolynomial
open MvPolynomial AspisV8R16 AspisV8R17 AspisR19 HighRepairInvariant
open AspisR19.TwoSwapSourceTable AspisR19.R645TwoSwapHighDirections
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R661TwoSwapMaskAddition
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R878SemanticChordPolynomial
open AspisV8R19.R875AugmentedSemanticMatrixHom
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

lemma actualCoin_eq_sourceChord (half alpha a b c : F) (d : Fin 255) (s : Fin 3)
    (i : Fin 271) :
    actualCoin (indexedMask half a b c (indexedDirection alpha d s)) i =
      sourceChord half (direction alpha d s) a b c (TwoSwapSourceG.coinIndex i).val := by
  simp only [actualCoin, indexedMask, fullMask, R562.inverseChordMessage,
    inverseTransport, if_neg (TwoSwapSourceG.coin_not_pivot i), Equiv.symm_apply_apply]
  rw [← rawFlatten_eq_flattenFull, rawFlatten_indexedDirection]

def semanticPolynomial (half : F) (weights : Fin 271 → JointPoly F)
    (d : Fin 255) (s : Fin 3) : JointPoly F :=
  ∑ i : Fin 271, weights i * chordPolynomial half d s (TwoSwapSourceG.coinIndex i).val

theorem eval_semanticPolynomial (half alpha u v kappa tau : F) (z : Fin 10 → F)
    (weights : Fin 271 → JointPoly F) (d : Fin 255) (s : Fin 3) :
    eval (assignment alpha u v kappa tau z) (semanticPolynomial half weights d s) =
      ∑ i : Fin 271, eval (assignment alpha u v kappa tau z) (weights i) *
        actualCoin (indexedMask half (1+u*v) (u*v-1) (-(u+v))
          (indexedDirection alpha d s)) i := by
  unfold semanticPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, eval_chordPolynomial, actualCoin_eq_sourceChord]

theorem semanticPolynomial_degree (half : F) (weights : Fin 271 → JointPoly F)
    (hw : ∀ i, (weights i).totalDegree ≤ 27) (d : Fin 255) (s : Fin 3) :
    (semanticPolynomial half weights d s).totalDegree ≤ 32 := by
  unfold semanticPolynomial
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans
    (Nat.add_le_add (hw i) (chordPolynomial_totalDegree_le half d s _))

def augmentedPolynomial (half quarter : F) (weights : Fin 271 → JointPoly F) :
    Matrix (R875AugmentedSemanticMatrixHom.Obs ⊕ Unit)
      (R875AugmentedSemanticMatrixHom.Obs ⊕ Unit) (JointPoly F) :=
  Matrix.fromBlocks
    (polynomialMatrix half quarter selectedColumns)
    (fun r (_ : Unit) => polynomialEntry half quarter 96 0 r)
    (fun (_ : Unit) c => semanticPolynomial half weights (selectedColumns c).1 (selectedColumns c).2)
    (fun (_ : Unit) (_ : Unit) => semanticPolynomial half weights 96 0)

theorem eval_augmentedPolynomial (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) (weights : Fin 271 → JointPoly F)
    (hw : ∀ i, eval (assignment alpha u v kappa tau z) (weights i) = maskWeights271 half coins i) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix
      (augmentedPolynomial half quarter weights) =
      augmentedMatrix half quarter alpha u v kappa tau z coins := by
  have hs (d : Fin 255) (slot : Fin 3) :
      eval (assignment alpha u v kappa tau z) (semanticPolynomial half weights d slot) =
      semanticEntry half (1+u*v) (u*v-1) (-(u+v)) coins (indexedDirection alpha d slot) := by
    rw [eval_semanticPolynomial]
    unfold semanticEntry
    apply Finset.sum_congr rfl
    intro i _
    rw [hw]
  unfold augmentedPolynomial augmentedMatrix
  ext row col
  rcases row with r | x <;> rcases col with c | y
  · exact eval_polynomialEntry half quarter alpha u v kappa tau z _ _ _
  · exact eval_polynomialEntry half quarter alpha u v kappa tau z 96 0 r
  · exact hs (selectedColumns c).1 (selectedColumns c).2
  · exact hs 96 0

theorem augmentedPolynomial_entry_degree (half quarter : F) (weights : Fin 271 → JointPoly F)
    (hw : ∀ i, (weights i).totalDegree ≤ 27)
    (r c : R875AugmentedSemanticMatrixHom.Obs ⊕ Unit) :
    (augmentedPolynomial half quarter weights r c).totalDegree ≤ 63 := by
  rcases r with r | unit <;> rcases c with c | unit
  · exact R843CompleteJointDegree.raw_entry_degree half quarter _ _ _
  · exact R843CompleteJointDegree.raw_entry_degree half quarter 96 0 r
  · exact (semanticPolynomial_degree half weights hw _ _).trans (by decide)
  · exact (semanticPolynomial_degree half weights hw 96 0).trans (by decide)

theorem augmentedPolynomial_det_degree (half quarter : F) (weights : Fin 271 → JointPoly F)
    (hw : ∀ i, (weights i).totalDegree ≤ 27) :
    (augmentedPolynomial half quarter weights).det.totalDegree ≤ 14049 := by
  have h := AspisV8R17.minor_totalDegree (augmentedPolynomial half quarter weights) 63
    (augmentedPolynomial_entry_degree half quarter weights hw)
  have hc : Fintype.card (R875AugmentedSemanticMatrixHom.Obs ⊕ Unit) = 223 := by
    rw [Fintype.card_sum, R746SelectedJointMinor.observation_card, Fintype.card_unique]
  rw [hc] at h
  exact h

#print axioms actualCoin_eq_sourceChord
#print axioms eval_semanticPolynomial
#print axioms semanticPolynomial_degree
#print axioms eval_augmentedPolynomial
#print axioms augmentedPolynomial_entry_degree
#print axioms augmentedPolynomial_det_degree
end
end AspisV8R19.R880AugmentedSemanticPolynomial

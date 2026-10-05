import AspisV8R19.R887Full223CombinationObservation
import AspisV8R19.R770NormalizedPairKernel
import AspisV8R19.R727TopBalance

set_option autoImplicit false
namespace AspisV8R19.R889Full223KernelProperties
open AspisV8R17 AspisCircleTensorBinding AspisR19
open AspisV8R19.R887Full223CombinationObservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R770NormalizedPairKernel
open AspisV8R19.R682FullQueryNormalization
open AspisR19.R370KernelEvaluation
open AspisR19.AugmentedQuerySection
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R727TopBalance
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev Obs := R875AugmentedSemanticMatrixHom.Obs

private lemma augmentedDirection_firstFold (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (col : Obs ⊕ Unit) (d : Fin 256) :
    firstFold 256 alpha (augmentedDirection alpha t ht noneOne col) d = 0 := by
  rcases col with c | unit
  · exact normalized_pair_firstFold alpha t ht noneOne
      (cast255 (selectedColumns c).1) d (selectedColumns c).2
  · exact normalized_pair_firstFold alpha t ht noneOne (cast255 96) d 0

private lemma augmentedDirection_query_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (col : Obs ⊕ Unit) (slot : Fin 4) (root : Fin 22) :
    evaluate256 (fun i => augmentedDirection alpha t ht noneOne col (i,slot)) (t root) = 0 := by
  rcases col with c | unit
  · exact normalized_pair_query_root alpha t ht noneOne
      (cast255 (selectedColumns c).1) (selectedColumns c).2 slot root
  · exact normalized_pair_query_root alpha t ht noneOne (cast255 96) 0 slot root

private lemma augmentedDirection_augmented_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (col : Obs ⊕ Unit) (slot : Fin 4) (root : Fin 23) :
    evaluate256 (fun i => augmentedDirection alpha t ht noneOne col (i,slot)) (roots t root) = 0 := by
  rcases col with c | unit
  · exact normalized_pair_augmented_root alpha t ht noneOne
      (cast255 (selectedColumns c).1) (selectedColumns c).2 slot root
  · exact normalized_pair_augmented_root alpha t ht noneOne (cast255 96) 0 slot root

theorem combination223_firstFold (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) (d : Fin 256) :
    firstFold 256 alpha (combination223 alpha t ht noneOne x) d = 0 := by
  simp only [firstFold, combination223, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hz : ∀ col : Obs ⊕ Unit,
      (∑ s : Fin 4, augmentedDirection alpha t ht noneOne col (d,s) * alpha^s.val) = 0 := by
    intro col
    exact augmentedDirection_firstFold alpha t ht noneOne col d
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem combination223_query_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) (slot : Fin 4) (root : Fin 22) :
    evaluate256 (fun d => combination223 alpha t ht noneOne x (d,slot)) (t root) = 0 := by
  unfold evaluate256 combination223
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hz : ∀ col : Obs ⊕ Unit,
      (∑ d : Fin 256, augmentedDirection alpha t ht noneOne col (d,slot) *
        naturalLineValue (t root) d.val) = 0 := by
    intro col
    exact augmentedDirection_query_root alpha t ht noneOne col slot root
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem combination223_augmented_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) (slot : Fin 4) (root : Fin 23) :
    evaluate256 (fun d => combination223 alpha t ht noneOne x (d,slot)) (roots t root) = 0 := by
  unfold evaluate256 combination223
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hz : ∀ col : Obs ⊕ Unit,
      (∑ d : Fin 256, augmentedDirection alpha t ht noneOne col (d,slot) *
        naturalLineValue (roots t root) d.val) = 0 := by
    intro col
    exact augmentedDirection_augmented_root alpha t ht noneOne col slot root
  simp only [hz, mul_zero, Finset.sum_const_zero]

private lemma augmentedDirection_degree255 (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (col : Obs ⊕ Unit) (slot : Fin 4) :
    augmentedDirection alpha t ht noneOne col ((255 : Fin 256),slot) = 0 := by
  rcases col with c | unit
  · have hne : (255 : Fin 256) ≠ cast255 (selectedColumns c).1 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [cast255] at hv
      omega
    unfold augmentedDirection normalizedPair
    rw [normalized_high t ht noneOne _ _ (by omega)]
    simp [hne]
  · have hne : (255 : Fin 256) ≠ cast255 (96 : Fin 255) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [cast255] at hv
      omega
    unfold augmentedDirection normalizedPair
    rw [normalized_high t ht noneOne _ _ (by omega)]
    simp [hne]

theorem flatten_combination223_top (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) (r : Nat) (hr : 1020 ≤ r) :
    flattenFull (combination223 alpha t ht noneOne x) r = 0 := by
  by_cases htop : r < 1024
  · rw [flattenFull, dif_pos htop]
    have hd : r / 4 = 255 := by omega
    have hi : (⟨r / 4, by omega⟩ : Fin 256) = (255 : Fin 256) := Fin.ext hd
    rw [hi]
    unfold combination223
    apply Finset.sum_eq_zero
    intro col _
    rw [augmentedDirection_degree255]
    ring
  · rw [flattenFull, dif_neg htop]

theorem rawMask_combination223_balanced (half a b c alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : Obs ⊕ Unit → F) :
    (∑ r ∈ TwoSwapSourceTable.inactive,
      rawMask half a b c (combination223 alpha t ht noneOne x) r) = 0 := by
  rw [rawMask_eq_indexedMask]
  exact indexed_balance_from_top half a b c (combination223 alpha t ht noneOne x)
    (flatten_combination223_top alpha t ht noneOne x 1021 (by omega))
    (flatten_combination223_top alpha t ht noneOne x 1022 (by omega))
    (flatten_combination223_top alpha t ht noneOne x 1023 (by omega))

#print axioms combination223_firstFold
#print axioms combination223_query_root
#print axioms combination223_augmented_root
#print axioms flatten_combination223_top
#print axioms rawMask_combination223_balanced
end
end AspisV8R19.R889Full223KernelProperties

import AspisV8R19.R826JointCombinationObservation
import AspisV8R19.R770NormalizedPairKernel

set_option autoImplicit false
namespace AspisV8R19.R827JointCombinationKernel
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R770NormalizedPairKernel
open AspisV8R19.R682FullQueryNormalization
open AspisR19.R370KernelEvaluation
open AspisR19.AugmentedQuerySection
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

abbrev ObservationRow := R738JointObservationModel.ObservationRow

theorem combination_firstFold (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) (d : Fin 256) :
    firstFold 256 alpha (combination alpha t ht noneOne x) d = 0 := by
  simp only [firstFold, combination, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hz : ∀ col : ObservationRow,
      (∑ s : Fin 4,
        normalizedPair alpha t ht noneOne
          (cast255 (selectedColumns col).1) (selectedColumns col).2 (d,s) * alpha^s.val) = 0 := by
    intro col
    exact normalized_pair_firstFold alpha t ht noneOne
      (cast255 (selectedColumns col).1) d (selectedColumns col).2
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem combination_query_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) (slot : Fin 4) (root : Fin 22) :
    evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (t root) = 0 := by
  unfold evaluate256 combination
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hz : ∀ col : ObservationRow,
      (∑ d : Fin 256,
        normalizedPair alpha t ht noneOne
          (cast255 (selectedColumns col).1) (selectedColumns col).2 (d,slot) *
          naturalLineValue (t root) d.val) = 0 := by
    intro col
    exact normalized_pair_query_root alpha t ht noneOne
      (cast255 (selectedColumns col).1) (selectedColumns col).2 slot root
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem combination_augmented_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) (slot : Fin 4) (root : Fin 23) :
    evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (roots t root) = 0 := by
  unfold evaluate256 combination
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hz : ∀ col : ObservationRow,
      (∑ d : Fin 256,
        normalizedPair alpha t ht noneOne
          (cast255 (selectedColumns col).1) (selectedColumns col).2 (d,slot) *
          naturalLineValue (roots t root) d.val) = 0 := by
    intro col
    exact normalized_pair_augmented_root alpha t ht noneOne
      (cast255 (selectedColumns col).1) (selectedColumns col).2 slot root
  simp only [hz, mul_zero, Finset.sum_const_zero]

#print axioms combination_firstFold
#print axioms combination_query_root
#print axioms combination_augmented_root
end
end AspisV8R19.R827JointCombinationKernel

import AspisV8R19.R767NormalizedSparseEntry
namespace AspisV8R19.R770NormalizedPairKernel
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R739AugmentedQuery256
open AspisV8R19.R682FullQueryNormalization
open AspisR19.AugmentedQuerySection
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def slotCoefficient (alpha : F) (s : Fin 3) (slot : Fin 4) : F :=
  (if slot = ⟨s.val+1,by omega⟩ then 1 else 0) -
  alpha^(s.val+1)*(if slot = 0 then 1 else 0)

lemma indexedPair_diagonal (alpha : F) (i : Fin 256) (s : Fin 3) (slot : Fin 4) :
    indexedPair alpha i s (i,slot) = slotCoefficient alpha s slot := by
  simp [indexedPair, indexedBasis, slotCoefficient]

theorem normalized_pair_firstFold (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d i : Fin 256) (s : Fin 3) :
    AspisR19.R370KernelEvaluation.firstFold 256 alpha
      (normalizedPair alpha t ht noneOne d s) i = 0 := by
  unfold AspisR19.R370KernelEvaluation.firstFold normalizedPair
  dsimp only
  rw [pair_block]
  simp

theorem normalized_pair_evaluate (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 256) (s : Fin 3) (slot : Fin 4) (x : F) :
    evaluate256 (fun i => normalizedPair alpha t ht noneOne d s (i,slot)) x =
      slotCoefficient alpha s slot * evaluate256 (normalized t ht noneOne d) x := by
  simp only [evaluate256, normalizedPair, indexedPair_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalized_pair_augmented_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 256) (s : Fin 3) (slot : Fin 4) (root : Fin 23) :
    evaluate256 (fun i => normalizedPair alpha t ht noneOne d s (i,slot))
      (roots t root) = 0 := by
  rw [normalized_pair_evaluate, R739AugmentedQuery256.normalized_augmented_root, mul_zero]

theorem normalized_pair_query_root (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 256) (s : Fin 3) (slot : Fin 4) (root : Fin 22) :
    evaluate256 (fun i => normalizedPair alpha t ht noneOne d s (i,slot))
      (t root) = 0 := by
  rw [normalized_pair_evaluate, R739AugmentedQuery256.normalized_query_root, mul_zero]

#print axioms indexedPair_diagonal
#print axioms normalized_pair_firstFold
#print axioms normalized_pair_evaluate
#print axioms normalized_pair_augmented_root
#print axioms normalized_pair_query_root
end
end AspisV8R19.R770NormalizedPairKernel

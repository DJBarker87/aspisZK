import AspisV8R19.R765NormalizedJointRepair
namespace AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R764RawJointWeights
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R739AugmentedQuery256
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

lemma basis_contraction (w : Index256 → F) (d : Fin 256) (s : Fin 4) :
    (∑ i : Fin 256, ∑ j : Fin 4, indexedBasis 256 d s (i,j) * w (i,j)) = w (d,s) := by
  simp [indexedBasis, Prod.mk.injEq, and_comm]

lemma pair_contraction (w : Index256 → F) (alpha : F) (d : Fin 256) (s : Fin 3) :
    (∑ i : Fin 256, ∑ j : Fin 4, indexedPair alpha d s (i,j) * w (i,j)) =
      w (d,⟨s.val+1,by omega⟩) - alpha^(s.val+1)*w (d,0) := by
  simp only [indexedPair, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [basis_contraction, basis_contraction]

theorem sparseObservation_pairedWeight (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3) (row : ObservationRow) :
    R743JointSparseEntryBinding.sparseObservation half quarter a b c kappa tau alpha z d s row =
      pairedWeight half quarter a b c kappa tau alpha z row (cast255 d) s -
      pairedWeight half quarter a b c kappa tau alpha z row 0 s := by
  rw [← R743JointSparseEntryBinding.rawObservation_indexedDirection]
  rw [rawObservation_weighted]
  simp only [R743JointSparseEntryBinding.indexedDirection, sub_mul, Finset.sum_sub_distrib]
  rw [pair_contraction, pair_contraction]
  rfl

theorem normalized_sparse_entry (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (row : ObservationRow) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (d : Fin 255) (s : Fin 3) :
    rawObservation half quarter a b c kappa tau z
      (normalizedPair alpha t ht noneOne (cast255 d) s) row =
      R743JointSparseEntryBinding.sparseObservation half quarter a b c kappa tau alpha z d s row -
      ∑ j : Fin 23, low t ht noneOne (cast255 d) j *
        R743JointSparseEntryBinding.sparseObservation half quarter a b c kappa tau alpha z ⟨j.val,by omega⟩ s row := by
  rw [normalized_observation_repair, sparseObservation_pairedWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [sparseObservation_pairedWeight]
  rfl

#print axioms basis_contraction
#print axioms pair_contraction
#print axioms sparseObservation_pairedWeight
#print axioms normalized_sparse_entry
end
end AspisV8R19.R767NormalizedSparseEntry

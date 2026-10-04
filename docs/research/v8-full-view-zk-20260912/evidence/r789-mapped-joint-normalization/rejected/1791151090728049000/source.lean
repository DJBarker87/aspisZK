import AspisV8R19.R784FixedJointNormalization
import AspisV8R19.R744JointEntryHom
namespace AspisV8R19.R789MappedJointNormalization
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R744JointEntryHom
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R748JointWitnessPointEntry (z)
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem mapped_low_joint_zero (f : M →+* K) (d : Fin 23) (s : Fin 3)
    (row : R738JointObservationModel.ObservationRow) :
    sparseObservation (f half) (f (536870912 : M)) 7 5 (-5) 5 0 7
      (fun i => f (z i)) ⟨d.val,by omega⟩ s row = 0 := by
  rcases row with j | ⟨p | k⟩
  · exact R773LowActiveKernel.low_active_observation_zero (f half) 7 5 (-5) 7 d s j
  · have h := map_sparse_point_row f half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val,by omega⟩ s p
    rw [R784FixedJointNormalization.fixed_low_joint_zero, map_zero] at h
    simpa only [map_ofNat, map_neg, map_zero] using h.symm
  · have h := map_sparse_coefficient_row f half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val,by omega⟩ s k
    rw [R784FixedJointNormalization.fixed_low_joint_zero, map_zero] at h
    simpa only [map_ofNat, map_neg, map_zero] using h.symm

theorem mapped_normalized_observation (f : M →+* K)
    (t : Fin 22 → K) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 255) (s : Fin 3) (row : R738JointObservationModel.ObservationRow) :
    rawObservation (f half) (f (536870912 : M)) 7 5 (-5) 5 0 (fun i=>f(z i))
      (normalizedPair 7 t ht noneOne (R741SparseCoefficientObservation.cast255 d) s) row =
    sparseObservation (f half) (f (536870912 : M)) 7 5 (-5) 5 0 7
      (fun i=>f(z i)) d s row := by
  rw [normalized_sparse_entry]
  simp only [mapped_low_joint_zero, mul_zero, Finset.sum_const_zero, sub_zero]

theorem mapped_normalized_matrix (f : M →+* K)
    (t : Fin 22 → K) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    normalizedSelectedMatrix (f half) (f (536870912 : M)) 7 2 3 5 0
      (fun i=>f(z i)) t ht noneOne =
    chosenSourceMatrix (f half) (f (536870912 : M)) 7 2 3 5 0 (fun i=>f(z i)) := by
  ext row col
  unfold normalizedSelectedMatrix chosenSourceMatrix
  have ha : (1+(2:K)*3) = 7 := by ring
  have hb : ((2:K)*3-1) = 5 := by ring
  have hc : (-((2:K)+3)) = -5 := by ring
  rw [ha,hb,hc,mapped_normalized_observation,
    R743JointSparseEntryBinding.rawObservation_indexedDirection]

#print axioms mapped_low_joint_zero
#print axioms mapped_normalized_observation
#print axioms mapped_normalized_matrix
end
end AspisV8R19.R789MappedJointNormalization

import AspisV8R15.ExactTowerBase
import AspisV8R19.R781NormalizedActivePreservation
import AspisV8R19.R782Point02LowKernel
import AspisV8R19.R783FixedOrdinaryLowKernel
namespace AspisV8R19.R784FixedJointNormalization
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R748JointWitnessPointEntry (z)
open AspisV8R19.R781NormalizedActivePreservation
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
local instance : Fact (Nat.Prime 2147483647) := AspisV8R15.ExactTowerBase.m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩

theorem fixed_low_joint_zero (d : Fin 23) (s : Fin 3) (row : R738JointObservationModel.ObservationRow) :
    sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z
      ⟨d.val,by omega⟩ s row = 0 := by
  rcases row with j | ⟨p | k⟩
  · exact R773LowActiveKernel.low_active_observation_zero half 7 5 (-5) 7 d s j
  · fin_cases p
    · exact R782Point02LowKernel.fixed_point0_low_sparse_zero d s
    · exact fixed_point1_low_sparse_zero d s
    · exact R782Point02LowKernel.fixed_point2_low_sparse_zero d s
  · exact R783FixedOrdinaryLowKernel.coefficient_low_zero d s k

theorem fixed_normalized_observation (t : Fin 22 → M) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 255) (s : Fin 3) (row : R738JointObservationModel.ObservationRow) :
    rawObservation half (536870912 : M) 7 5 (-5) 5 0 z
      (normalizedPair 7 t ht noneOne (R741SparseCoefficientObservation.cast255 d) s) row =
      sparseObservation half (536870912 : M) 7 5 (-5) 5 0 7 z d s row := by
  rw [normalized_sparse_entry]
  simp only [fixed_low_joint_zero, mul_zero, Finset.sum_const_zero, sub_zero]

theorem fixed_normalized_matrix (t : Fin 22 → M) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    normalizedSelectedMatrix half (536870912 : M) 7 2 3 5 0 z t ht noneOne =
      chosenSourceMatrix half (536870912 : M) 7 2 3 5 0 z := by
  ext row col
  unfold normalizedSelectedMatrix chosenSourceMatrix
  have ha : (1+(2:M)*3) = 7 := by decide
  have hb : ((2:M)*3-1) = 5 := by decide
  have hc : (-((2:M)+3)) = -5 := by decide
  rw [ha,hb,hc,fixed_normalized_observation,
    R743JointSparseEntryBinding.rawObservation_indexedDirection]

theorem fixed_normalized_det (t : Fin 22 → M) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    (normalizedSelectedMatrix half (536870912 : M) 7 2 3 5 0 z t ht noneOne).det =
      (chosenSourceMatrix half (536870912 : M) 7 2 3 5 0 z).det := by
  rw [fixed_normalized_matrix]

#print axioms fixed_low_joint_zero
#print axioms fixed_normalized_observation
#print axioms fixed_normalized_matrix
#print axioms fixed_normalized_det
end
end AspisV8R19.R784FixedJointNormalization

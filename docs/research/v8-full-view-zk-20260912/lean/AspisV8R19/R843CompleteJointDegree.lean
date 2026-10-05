import AspisV8R19.R837ActiveJointEntryDegree
import AspisV8R19.R840JointPointRowDegree
import AspisV8R19.R841RawOrdinaryWeightDegree
import AspisV8R19.R842SparseCoefficientDegree
import AspisV8R19.R834NormalizedJointDegree

set_option autoImplicit false
namespace AspisV8R19.R843CompleteJointDegree
open MvPolynomial
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R833RootFixedJointPolynomial
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem raw_entry_degree (half quarter : F) (d : Fin 255) (s : Fin 3)
    (row : ObservationRow) :
    (polynomialEntry half quarter d s row).totalDegree ≤ 63 := by
  rcases row with j | p | k
  · exact (R837ActiveJointEntryDegree.active_polynomialEntry_totalDegree_le half quarter d s j).trans (by decide)
  · exact (R840JointPointRowDegree.point_row_polynomialEntry_totalDegree_le half quarter d s p).trans (by decide)
  · exact R842SparseCoefficientDegree.sparse_coefficient_degree half quarter 60
      (R841RawOrdinaryWeightDegree.raw_ordinary_weight_degree half) d s k

theorem normalized_det_degree (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (rootFixedMatrix half quarter t ht noneOne).det.totalDegree ≤ 13986 := by
  exact R834NormalizedJointDegree.rootFixedMatrix_det_totalDegree_le
    half quarter t ht noneOne 63 (raw_entry_degree half quarter)

#print axioms raw_entry_degree
#print axioms normalized_det_degree
end
end AspisV8R19.R843CompleteJointDegree

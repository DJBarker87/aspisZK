/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryBridge
import AspisV8R19.WitnessInverseRow00
import AspisV8R19.WitnessInverseRow01
import AspisV8R19.WitnessInverseRow02
import AspisV8R19.WitnessInverseRow03
import AspisV8R19.WitnessInverseRow04
import AspisV8R19.WitnessInverseRow05
import AspisV8R19.WitnessInverseRow06
import AspisV8R19.WitnessInverseRow07
import AspisV8R19.WitnessInverseRow08
import AspisV8R19.WitnessInverseRow09
import AspisV8R19.WitnessInverseRow10
import AspisV8R19.WitnessInverseRow11
import AspisV8R19.WitnessInverseRow12
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem matrix_right_inverse : matrix*inverseMatrix=1 := by
  funext i j
  fin_cases i
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j
  · exact inverse_row10 j
  · exact inverse_row11 j
  · exact inverse_row12 j
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  letI : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
  exact ResidualNonsingular.right_inverse_det_ne_zero matrix inverseMatrix matrix_right_inverse
def assignment : Fin 36 → M := PointWeightCertificate.vector [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 5, 7, 2, 3, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
theorem assigned_matrix : SourceResidualPolynomial.assignedMinor half quarter assignment = matrix := by
  have hz : (fun i : Fin 10 => assignment ⟨i.val,by omega⟩) = WitnessPointData.z := by
    funext i
    fin_cases i <;> decide
  have hr : (fun i : Fin 22 => assignment ⟨14+i.val,by omega⟩) = WitnessRootData.roots := by
    funext i
    fin_cases i <;> decide
  unfold SourceResidualPolynomial.assignedMinor SourceResidualPolynomial.normalizedMinor
  rw [hz,hr]
  change minor ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) = matrix
  exact minor_matrix
theorem assigned_det_ne_zero : (SourceResidualPolynomial.assignedMinor half quarter assignment).det ≠ 0 := by
  rw [assigned_matrix]
  exact matrix_det_ne_zero
theorem restricted_polynomial_ne_zero : (SourceResidualPolynomial.polyMinor half quarter).det ≠ 0 :=
  ResidualNonsingular.polynomial_nonzero half quarter assignment assigned_det_ne_zero
#print axioms matrix_right_inverse
#print axioms matrix_det_ne_zero
#print axioms assigned_matrix
#print axioms assigned_det_ne_zero
#print axioms restricted_polynomial_ne_zero
end
end AspisR19.WitnessEntryData

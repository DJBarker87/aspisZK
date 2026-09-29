/- Generated fixed high-coordinate certificate. No query recurrence is evaluated. -/
import AspisV8R19.HighWitnessEntries
import AspisV8R19.HighWitnessInverseRow00
import AspisV8R19.HighWitnessInverseRow01
import AspisV8R19.HighWitnessInverseRow02
import AspisV8R19.HighWitnessInverseRow03
import AspisV8R19.HighWitnessInverseRow04
import AspisV8R19.HighWitnessInverseRow05
import AspisV8R19.HighWitnessInverseRow06
import AspisV8R19.HighWitnessInverseRow07
import AspisV8R19.HighWitnessInverseRow08
import AspisV8R19.HighWitnessInverseRow09
import AspisV8R19.HighWitnessInverseRow10
import AspisV8R19.HighWitnessInverseRow11
import AspisV8R19.HighWitnessInverseRow12
namespace AspisR19.HighWitnessData
open RootCertificate
noncomputable section
theorem right_inverse : expectedMatrix*inverseMatrix=1 := by
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
theorem expected_det_ne_zero : expectedMatrix.det ≠ 0 := by
  letI : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
  exact ResidualNonsingular.right_inverse_det_ne_zero _ _ right_inverse
theorem model_det_ne_zero : SparseHighWitness.matrix.det ≠ 0 := by
  rw [model_matrix]
  exact expected_det_ne_zero
#print axioms right_inverse
#print axioms expected_det_ne_zero
#print axioms model_det_ne_zero
end
end AspisR19.HighWitnessData

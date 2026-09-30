/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapMatrixEntries
import AspisV8R19.ResidualNonsingular
import AspisV8R19.TwoSwapInverseRow00
import AspisV8R19.TwoSwapInverseRow01
import AspisV8R19.TwoSwapInverseRow02
import AspisV8R19.TwoSwapInverseRow03
import AspisV8R19.TwoSwapInverseRow04
import AspisV8R19.TwoSwapInverseRow05
import AspisV8R19.TwoSwapInverseRow06
import AspisV8R19.TwoSwapInverseRow07
import AspisV8R19.TwoSwapInverseRow08
import AspisV8R19.TwoSwapInverseRow09
import AspisV8R19.TwoSwapInverseRow10
import AspisV8R19.TwoSwapInverseRow11
import AspisV8R19.TwoSwapInverseRow12
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
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
theorem model_det_ne_zero : matrix.det≠0 := by
  letI : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
  rw [matrix_entries]
  exact ResidualNonsingular.right_inverse_det_ne_zero _ _ right_inverse
#print axioms right_inverse
#print axioms model_det_ne_zero
end
end AspisR19.TwoSwapWitness

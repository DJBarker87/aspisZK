import AspisV8R19.R815BlockZeroSourceView
import AspisV8R19.R817BlockZeroRow00Binding
import AspisV8R19.R818BlockZeroRow01Binding
import AspisV8R19.R818BlockZeroRow02Binding
import AspisV8R19.R818BlockZeroRow03Binding
import AspisV8R19.R818BlockZeroRow04Binding
import AspisV8R19.R818BlockZeroRow05Binding
import AspisV8R19.R752SCC00Inverse

set_option autoImplicit false
namespace AspisV8R19.R819BlockZeroBinding
open AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R817BlockZeroRow00Binding
open AspisV8R19.R818BlockZeroRow01Binding
open AspisV8R19.R818BlockZeroRow02Binding
open AspisV8R19.R818BlockZeroRow03Binding
open AspisV8R19.R818BlockZeroRow04Binding
open AspisV8R19.R818BlockZeroRow05Binding
open R752SCC00Matrix R752SCC00Inverse

 theorem source_block00_eq_certificate : block00SourceMatrix = A_scc := by
  funext i
  fin_cases i
  · exact source_block00_row0_eq_certificate
  · exact source_block00_row1_eq_certificate
  · exact source_block00_row2_eq_certificate
  · exact source_block00_row3_eq_certificate
  · exact source_block00_row4_eq_certificate
  · exact source_block00_row5_eq_certificate

theorem diagonal_source_block00_eq_certificate : diagonalSourceBlock 0 = A_scc :=
  diagonalSourceBlock00_eq_sourceView.trans source_block00_eq_certificate

theorem diagonal_source_block00_det_isUnit : IsUnit (Matrix.det (diagonalSourceBlock 0)) := by
  have h := congrArg Matrix.det diagonal_source_block00_eq_certificate
  rw [h]
  exact determinant_isUnit

#print axioms source_block00_eq_certificate
#print axioms diagonal_source_block00_eq_certificate
#print axioms diagonal_source_block00_det_isUnit
end AspisV8R19.R819BlockZeroBinding

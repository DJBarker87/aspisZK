import AspisV8R19.R752SCC00Inverse
import AspisV8R19.R752SCC01Inverse
import AspisV8R19.R752SCC02Inverse
import AspisV8R19.R752SCC03Inverse
import AspisV8R19.R752SCC04Inverse
import AspisV8R19.R752SCC05Inverse
import AspisV8R19.R751JointBlock39Inverse
import AspisV8R19.R752SCC07Inverse
import AspisV8R19.R752SCC08Inverse
import AspisV8R19.R752SCC09Inverse
import AspisV8R19.R752SCC10Inverse
import AspisV8R19.R752SCC11Inverse
import AspisV8R19.R752SCC12Inverse
import AspisV8R19.R752SCC13Inverse
import AspisV8R19.R752SCC14Inverse
import AspisV8R19.R752SCC15Inverse
import AspisV8R19.R752SCC16Inverse
import AspisV8R19.R752SCC17Inverse
import AspisV8R19.R752SCC18Inverse
import AspisV8R19.R752SCC19Inverse
import AspisV8R19.R752SCC20Inverse
import AspisV8R19.R752SCC21Inverse
import AspisV8R19.R752SCC22Inverse
import AspisV8R19.R752SCC23Inverse
import AspisV8R19.R752SCC24Inverse
import AspisV8R19.R752SCC25Inverse
import AspisV8R19.R752SCC26Inverse
import AspisV8R19.R752SCC27Inverse
import AspisV8R19.R752SCC28Inverse
import AspisV8R19.R752SCC29Inverse
import AspisV8R19.R752SCC30Inverse
import AspisV8R19.R752SCC31Inverse
import AspisV8R19.R752SCC32Inverse
import AspisV8R19.R752SCC33Inverse
import AspisV8R19.R752SCC34Inverse
import AspisV8R19.R752SCC35Inverse
import AspisV8R19.R752SCC36Inverse
import AspisV8R19.R752SCC37Inverse
import AspisV8R19.R752SCC38Inverse
import AspisV8R19.R752SCC39Inverse
import AspisV8R19.R752SCC40Inverse

namespace AspisV8R19.R762AllLiteralBlockUnits
open scoped BigOperators
set_option maxRecDepth 4096
noncomputable section
abbrev M := ZMod 2147483647
def blockDet : Fin 41 → M
  | ⟨0, _⟩ => Matrix.det R752SCC00Matrix.A_scc
  | ⟨1, _⟩ => Matrix.det R752SCC01Matrix.A_scc
  | ⟨2, _⟩ => Matrix.det R752SCC02Matrix.A_scc
  | ⟨3, _⟩ => Matrix.det R752SCC03Matrix.A_scc
  | ⟨4, _⟩ => Matrix.det R752SCC04Matrix.A_scc
  | ⟨5, _⟩ => Matrix.det R752SCC05Matrix.A_scc
  | ⟨6, _⟩ => Matrix.det R747JointBlock39Preflight.A
  | ⟨7, _⟩ => Matrix.det R752SCC07Matrix.A_scc
  | ⟨8, _⟩ => Matrix.det R752SCC08Matrix.A_scc
  | ⟨9, _⟩ => Matrix.det R752SCC09Matrix.A_scc
  | ⟨10, _⟩ => Matrix.det R752SCC10Matrix.A_scc
  | ⟨11, _⟩ => Matrix.det R752SCC11Matrix.A_scc
  | ⟨12, _⟩ => Matrix.det R752SCC12Matrix.A_scc
  | ⟨13, _⟩ => Matrix.det R752SCC13Matrix.A_scc
  | ⟨14, _⟩ => Matrix.det R752SCC14Matrix.A_scc
  | ⟨15, _⟩ => Matrix.det R752SCC15Matrix.A_scc
  | ⟨16, _⟩ => Matrix.det R752SCC16Matrix.A_scc
  | ⟨17, _⟩ => Matrix.det R752SCC17Matrix.A_scc
  | ⟨18, _⟩ => Matrix.det R752SCC18Matrix.A_scc
  | ⟨19, _⟩ => Matrix.det R752SCC19Matrix.A_scc
  | ⟨20, _⟩ => Matrix.det R752SCC20Matrix.A_scc
  | ⟨21, _⟩ => Matrix.det R752SCC21Matrix.A_scc
  | ⟨22, _⟩ => Matrix.det R752SCC22Matrix.A_scc
  | ⟨23, _⟩ => Matrix.det R752SCC23Matrix.A_scc
  | ⟨24, _⟩ => Matrix.det R752SCC24Matrix.A_scc
  | ⟨25, _⟩ => Matrix.det R752SCC25Matrix.A_scc
  | ⟨26, _⟩ => Matrix.det R752SCC26Matrix.A_scc
  | ⟨27, _⟩ => Matrix.det R752SCC27Matrix.A_scc
  | ⟨28, _⟩ => Matrix.det R752SCC28Matrix.A_scc
  | ⟨29, _⟩ => Matrix.det R752SCC29Matrix.A_scc
  | ⟨30, _⟩ => Matrix.det R752SCC30Matrix.A_scc
  | ⟨31, _⟩ => Matrix.det R752SCC31Matrix.A_scc
  | ⟨32, _⟩ => Matrix.det R752SCC32Matrix.A_scc
  | ⟨33, _⟩ => Matrix.det R752SCC33Matrix.A_scc
  | ⟨34, _⟩ => Matrix.det R752SCC34Matrix.A_scc
  | ⟨35, _⟩ => Matrix.det R752SCC35Matrix.A_scc
  | ⟨36, _⟩ => Matrix.det R752SCC36Matrix.A_scc
  | ⟨37, _⟩ => Matrix.det R752SCC37Matrix.A_scc
  | ⟨38, _⟩ => Matrix.det R752SCC38Matrix.A_scc
  | ⟨39, _⟩ => Matrix.det R752SCC39Matrix.A_scc
  | ⟨40, _⟩ => Matrix.det R752SCC40Matrix.A_scc

theorem block_det_unit (i : Fin 41) : IsUnit (blockDet i) := by
  fin_cases i
  · change IsUnit (Matrix.det R752SCC00Matrix.A_scc)
    exact R752SCC00Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC01Matrix.A_scc)
    exact R752SCC01Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC02Matrix.A_scc)
    exact R752SCC02Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC03Matrix.A_scc)
    exact R752SCC03Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC04Matrix.A_scc)
    exact R752SCC04Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC05Matrix.A_scc)
    exact R752SCC05Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R747JointBlock39Preflight.A)
    exact Matrix.isUnit_det_of_left_inverse R751JointBlock39Inverse.left_inverse
  · change IsUnit (Matrix.det R752SCC07Matrix.A_scc)
    exact R752SCC07Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC08Matrix.A_scc)
    exact R752SCC08Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC09Matrix.A_scc)
    exact R752SCC09Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC10Matrix.A_scc)
    exact R752SCC10Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC11Matrix.A_scc)
    exact R752SCC11Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC12Matrix.A_scc)
    exact R752SCC12Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC13Matrix.A_scc)
    exact R752SCC13Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC14Matrix.A_scc)
    exact R752SCC14Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC15Matrix.A_scc)
    exact R752SCC15Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC16Matrix.A_scc)
    exact R752SCC16Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC17Matrix.A_scc)
    exact R752SCC17Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC18Matrix.A_scc)
    exact R752SCC18Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC19Matrix.A_scc)
    exact R752SCC19Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC20Matrix.A_scc)
    exact R752SCC20Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC21Matrix.A_scc)
    exact R752SCC21Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC22Matrix.A_scc)
    exact R752SCC22Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC23Matrix.A_scc)
    exact R752SCC23Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC24Matrix.A_scc)
    exact R752SCC24Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC25Matrix.A_scc)
    exact R752SCC25Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC26Matrix.A_scc)
    exact R752SCC26Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC27Matrix.A_scc)
    exact R752SCC27Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC28Matrix.A_scc)
    exact R752SCC28Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC29Matrix.A_scc)
    exact R752SCC29Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC30Matrix.A_scc)
    exact R752SCC30Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC31Matrix.A_scc)
    exact R752SCC31Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC32Matrix.A_scc)
    exact R752SCC32Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC33Matrix.A_scc)
    exact R752SCC33Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC34Matrix.A_scc)
    exact R752SCC34Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC35Matrix.A_scc)
    exact R752SCC35Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC36Matrix.A_scc)
    exact R752SCC36Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC37Matrix.A_scc)
    exact R752SCC37Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC38Matrix.A_scc)
    exact R752SCC38Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC39Matrix.A_scc)
    exact R752SCC39Inverse.determinant_isUnit
  · change IsUnit (Matrix.det R752SCC40Matrix.A_scc)
    exact R752SCC40Inverse.determinant_isUnit

#print axioms block_det_unit

theorem diagonal_product_unit : IsUnit (∏ i : Fin 41, blockDet i) :=
  IsUnit.prod_univ_iff.mpr block_det_unit

#print axioms diagonal_product_unit
end
end AspisV8R19.R762AllLiteralBlockUnits

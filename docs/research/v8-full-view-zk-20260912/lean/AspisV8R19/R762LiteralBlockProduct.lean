import AspisV8R19.R752SCC00Inverse
import AspisV8R19.R752SCC01Inverse
import AspisV8R19.R752SCC02Inverse
import AspisV8R19.R752SCC03Inverse
import AspisV8R19.R752SCC04Inverse
import AspisV8R19.R752SCC05Inverse
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
import AspisV8R19.R751JointBlock39Inverse
import AspisV8R19.R747JointBlock39Preflight

namespace AspisV8R19.R762LiteralBlockProduct
noncomputable section

abbrev M := ZMod 2147483647

def factor_00 : M := Matrix.det R752SCC00Matrix.A_scc
def factor_01 : M := Matrix.det R752SCC01Matrix.A_scc
def factor_02 : M := Matrix.det R752SCC02Matrix.A_scc
def factor_03 : M := Matrix.det R752SCC03Matrix.A_scc
def factor_04 : M := Matrix.det R752SCC04Matrix.A_scc
def factor_05 : M := Matrix.det R752SCC05Matrix.A_scc
def factor_06 : M := Matrix.det R747JointBlock39Preflight.A
def factor_07 : M := Matrix.det R752SCC07Matrix.A_scc
def factor_08 : M := Matrix.det R752SCC08Matrix.A_scc
def factor_09 : M := Matrix.det R752SCC09Matrix.A_scc
def factor_10 : M := Matrix.det R752SCC10Matrix.A_scc
def factor_11 : M := Matrix.det R752SCC11Matrix.A_scc
def factor_12 : M := Matrix.det R752SCC12Matrix.A_scc
def factor_13 : M := Matrix.det R752SCC13Matrix.A_scc
def factor_14 : M := Matrix.det R752SCC14Matrix.A_scc
def factor_15 : M := Matrix.det R752SCC15Matrix.A_scc
def factor_16 : M := Matrix.det R752SCC16Matrix.A_scc
def factor_17 : M := Matrix.det R752SCC17Matrix.A_scc
def factor_18 : M := Matrix.det R752SCC18Matrix.A_scc
def factor_19 : M := Matrix.det R752SCC19Matrix.A_scc
def factor_20 : M := Matrix.det R752SCC20Matrix.A_scc
def factor_21 : M := Matrix.det R752SCC21Matrix.A_scc
def factor_22 : M := Matrix.det R752SCC22Matrix.A_scc
def factor_23 : M := Matrix.det R752SCC23Matrix.A_scc
def factor_24 : M := Matrix.det R752SCC24Matrix.A_scc
def factor_25 : M := Matrix.det R752SCC25Matrix.A_scc
def factor_26 : M := Matrix.det R752SCC26Matrix.A_scc
def factor_27 : M := Matrix.det R752SCC27Matrix.A_scc
def factor_28 : M := Matrix.det R752SCC28Matrix.A_scc
def factor_29 : M := Matrix.det R752SCC29Matrix.A_scc
def factor_30 : M := Matrix.det R752SCC30Matrix.A_scc
def factor_31 : M := Matrix.det R752SCC31Matrix.A_scc
def factor_32 : M := Matrix.det R752SCC32Matrix.A_scc
def factor_33 : M := Matrix.det R752SCC33Matrix.A_scc
def factor_34 : M := Matrix.det R752SCC34Matrix.A_scc
def factor_35 : M := Matrix.det R752SCC35Matrix.A_scc
def factor_36 : M := Matrix.det R752SCC36Matrix.A_scc
def factor_37 : M := Matrix.det R752SCC37Matrix.A_scc
def factor_38 : M := Matrix.det R752SCC38Matrix.A_scc
def factor_39 : M := Matrix.det R752SCC39Matrix.A_scc
def factor_40 : M := Matrix.det R752SCC40Matrix.A_scc

theorem factor_00_unit : IsUnit factor_00 := by
  exact R752SCC00Inverse.determinant_isUnit
#print axioms factor_00_unit

theorem factor_01_unit : IsUnit factor_01 := by
  exact R752SCC01Inverse.determinant_isUnit
#print axioms factor_01_unit

theorem factor_02_unit : IsUnit factor_02 := by
  exact R752SCC02Inverse.determinant_isUnit
#print axioms factor_02_unit

theorem factor_03_unit : IsUnit factor_03 := by
  exact R752SCC03Inverse.determinant_isUnit
#print axioms factor_03_unit

theorem factor_04_unit : IsUnit factor_04 := by
  exact R752SCC04Inverse.determinant_isUnit
#print axioms factor_04_unit

theorem factor_05_unit : IsUnit factor_05 := by
  exact R752SCC05Inverse.determinant_isUnit
#print axioms factor_05_unit

theorem factor_06_unit : IsUnit factor_06 := by
  exact Matrix.isUnit_det_of_left_inverse R751JointBlock39Inverse.left_inverse
#print axioms factor_06_unit

theorem factor_07_unit : IsUnit factor_07 := by
  exact R752SCC07Inverse.determinant_isUnit
#print axioms factor_07_unit

theorem factor_08_unit : IsUnit factor_08 := by
  exact R752SCC08Inverse.determinant_isUnit
#print axioms factor_08_unit

theorem factor_09_unit : IsUnit factor_09 := by
  exact R752SCC09Inverse.determinant_isUnit
#print axioms factor_09_unit

theorem factor_10_unit : IsUnit factor_10 := by
  exact R752SCC10Inverse.determinant_isUnit
#print axioms factor_10_unit

theorem factor_11_unit : IsUnit factor_11 := by
  exact R752SCC11Inverse.determinant_isUnit
#print axioms factor_11_unit

theorem factor_12_unit : IsUnit factor_12 := by
  exact R752SCC12Inverse.determinant_isUnit
#print axioms factor_12_unit

theorem factor_13_unit : IsUnit factor_13 := by
  exact R752SCC13Inverse.determinant_isUnit
#print axioms factor_13_unit

theorem factor_14_unit : IsUnit factor_14 := by
  exact R752SCC14Inverse.determinant_isUnit
#print axioms factor_14_unit

theorem factor_15_unit : IsUnit factor_15 := by
  exact R752SCC15Inverse.determinant_isUnit
#print axioms factor_15_unit

theorem factor_16_unit : IsUnit factor_16 := by
  exact R752SCC16Inverse.determinant_isUnit
#print axioms factor_16_unit

theorem factor_17_unit : IsUnit factor_17 := by
  exact R752SCC17Inverse.determinant_isUnit
#print axioms factor_17_unit

theorem factor_18_unit : IsUnit factor_18 := by
  exact R752SCC18Inverse.determinant_isUnit
#print axioms factor_18_unit

theorem factor_19_unit : IsUnit factor_19 := by
  exact R752SCC19Inverse.determinant_isUnit
#print axioms factor_19_unit

theorem factor_20_unit : IsUnit factor_20 := by
  exact R752SCC20Inverse.determinant_isUnit
#print axioms factor_20_unit

theorem factor_21_unit : IsUnit factor_21 := by
  exact R752SCC21Inverse.determinant_isUnit
#print axioms factor_21_unit

theorem factor_22_unit : IsUnit factor_22 := by
  exact R752SCC22Inverse.determinant_isUnit
#print axioms factor_22_unit

theorem factor_23_unit : IsUnit factor_23 := by
  exact R752SCC23Inverse.determinant_isUnit
#print axioms factor_23_unit

theorem factor_24_unit : IsUnit factor_24 := by
  exact R752SCC24Inverse.determinant_isUnit
#print axioms factor_24_unit

theorem factor_25_unit : IsUnit factor_25 := by
  exact R752SCC25Inverse.determinant_isUnit
#print axioms factor_25_unit

theorem factor_26_unit : IsUnit factor_26 := by
  exact R752SCC26Inverse.determinant_isUnit
#print axioms factor_26_unit

theorem factor_27_unit : IsUnit factor_27 := by
  exact R752SCC27Inverse.determinant_isUnit
#print axioms factor_27_unit

theorem factor_28_unit : IsUnit factor_28 := by
  exact R752SCC28Inverse.determinant_isUnit
#print axioms factor_28_unit

theorem factor_29_unit : IsUnit factor_29 := by
  exact R752SCC29Inverse.determinant_isUnit
#print axioms factor_29_unit

theorem factor_30_unit : IsUnit factor_30 := by
  exact R752SCC30Inverse.determinant_isUnit
#print axioms factor_30_unit

theorem factor_31_unit : IsUnit factor_31 := by
  exact R752SCC31Inverse.determinant_isUnit
#print axioms factor_31_unit

theorem factor_32_unit : IsUnit factor_32 := by
  exact R752SCC32Inverse.determinant_isUnit
#print axioms factor_32_unit

theorem factor_33_unit : IsUnit factor_33 := by
  exact R752SCC33Inverse.determinant_isUnit
#print axioms factor_33_unit

theorem factor_34_unit : IsUnit factor_34 := by
  exact R752SCC34Inverse.determinant_isUnit
#print axioms factor_34_unit

theorem factor_35_unit : IsUnit factor_35 := by
  exact R752SCC35Inverse.determinant_isUnit
#print axioms factor_35_unit

theorem factor_36_unit : IsUnit factor_36 := by
  exact R752SCC36Inverse.determinant_isUnit
#print axioms factor_36_unit

theorem factor_37_unit : IsUnit factor_37 := by
  exact R752SCC37Inverse.determinant_isUnit
#print axioms factor_37_unit

theorem factor_38_unit : IsUnit factor_38 := by
  exact R752SCC38Inverse.determinant_isUnit
#print axioms factor_38_unit

theorem factor_39_unit : IsUnit factor_39 := by
  exact R752SCC39Inverse.determinant_isUnit
#print axioms factor_39_unit

theorem factor_40_unit : IsUnit factor_40 := by
  exact R752SCC40Inverse.determinant_isUnit
#print axioms factor_40_unit

def chunk_00_03 : M := ((factor_00 * factor_01) * (factor_02 * factor_03))
theorem chunk_00_03_unit : IsUnit chunk_00_03 := by
  have h00_01 : IsUnit (factor_00 * factor_01) := IsUnit.mul factor_00_unit factor_01_unit
  have h02_03 : IsUnit (factor_02 * factor_03) := IsUnit.mul factor_02_unit factor_03_unit
  exact IsUnit.mul h00_01 h02_03
#print axioms chunk_00_03_unit

def chunk_04_07 : M := ((factor_04 * factor_05) * (factor_06 * factor_07))
theorem chunk_04_07_unit : IsUnit chunk_04_07 := by
  have h04_05 : IsUnit (factor_04 * factor_05) := IsUnit.mul factor_04_unit factor_05_unit
  have h06_07 : IsUnit (factor_06 * factor_07) := IsUnit.mul factor_06_unit factor_07_unit
  exact IsUnit.mul h04_05 h06_07
#print axioms chunk_04_07_unit

def chunk_08_11 : M := ((factor_08 * factor_09) * (factor_10 * factor_11))
theorem chunk_08_11_unit : IsUnit chunk_08_11 := by
  have h08_09 : IsUnit (factor_08 * factor_09) := IsUnit.mul factor_08_unit factor_09_unit
  have h10_11 : IsUnit (factor_10 * factor_11) := IsUnit.mul factor_10_unit factor_11_unit
  exact IsUnit.mul h08_09 h10_11
#print axioms chunk_08_11_unit

def chunk_12_15 : M := ((factor_12 * factor_13) * (factor_14 * factor_15))
theorem chunk_12_15_unit : IsUnit chunk_12_15 := by
  have h12_13 : IsUnit (factor_12 * factor_13) := IsUnit.mul factor_12_unit factor_13_unit
  have h14_15 : IsUnit (factor_14 * factor_15) := IsUnit.mul factor_14_unit factor_15_unit
  exact IsUnit.mul h12_13 h14_15
#print axioms chunk_12_15_unit

def chunk_16_19 : M := ((factor_16 * factor_17) * (factor_18 * factor_19))
theorem chunk_16_19_unit : IsUnit chunk_16_19 := by
  have h16_17 : IsUnit (factor_16 * factor_17) := IsUnit.mul factor_16_unit factor_17_unit
  have h18_19 : IsUnit (factor_18 * factor_19) := IsUnit.mul factor_18_unit factor_19_unit
  exact IsUnit.mul h16_17 h18_19
#print axioms chunk_16_19_unit

def chunk_20_23 : M := ((factor_20 * factor_21) * (factor_22 * factor_23))
theorem chunk_20_23_unit : IsUnit chunk_20_23 := by
  have h20_21 : IsUnit (factor_20 * factor_21) := IsUnit.mul factor_20_unit factor_21_unit
  have h22_23 : IsUnit (factor_22 * factor_23) := IsUnit.mul factor_22_unit factor_23_unit
  exact IsUnit.mul h20_21 h22_23
#print axioms chunk_20_23_unit

def chunk_24_27 : M := ((factor_24 * factor_25) * (factor_26 * factor_27))
theorem chunk_24_27_unit : IsUnit chunk_24_27 := by
  have h24_25 : IsUnit (factor_24 * factor_25) := IsUnit.mul factor_24_unit factor_25_unit
  have h26_27 : IsUnit (factor_26 * factor_27) := IsUnit.mul factor_26_unit factor_27_unit
  exact IsUnit.mul h24_25 h26_27
#print axioms chunk_24_27_unit

def chunk_28_31 : M := ((factor_28 * factor_29) * (factor_30 * factor_31))
theorem chunk_28_31_unit : IsUnit chunk_28_31 := by
  have h28_29 : IsUnit (factor_28 * factor_29) := IsUnit.mul factor_28_unit factor_29_unit
  have h30_31 : IsUnit (factor_30 * factor_31) := IsUnit.mul factor_30_unit factor_31_unit
  exact IsUnit.mul h28_29 h30_31
#print axioms chunk_28_31_unit

def chunk_32_35 : M := ((factor_32 * factor_33) * (factor_34 * factor_35))
theorem chunk_32_35_unit : IsUnit chunk_32_35 := by
  have h32_33 : IsUnit (factor_32 * factor_33) := IsUnit.mul factor_32_unit factor_33_unit
  have h34_35 : IsUnit (factor_34 * factor_35) := IsUnit.mul factor_34_unit factor_35_unit
  exact IsUnit.mul h32_33 h34_35
#print axioms chunk_32_35_unit

def chunk_36_39 : M := ((factor_36 * factor_37) * (factor_38 * factor_39))
theorem chunk_36_39_unit : IsUnit chunk_36_39 := by
  have h36_37 : IsUnit (factor_36 * factor_37) := IsUnit.mul factor_36_unit factor_37_unit
  have h38_39 : IsUnit (factor_38 * factor_39) := IsUnit.mul factor_38_unit factor_39_unit
  exact IsUnit.mul h36_37 h38_39
#print axioms chunk_36_39_unit

def chunk_40_40 : M := factor_40
theorem chunk_40_40_unit : IsUnit chunk_40_40 := by
  exact factor_40_unit
#print axioms chunk_40_40_unit

def literal_product : M := (((chunk_00_03 * chunk_04_07) * (chunk_08_11 * (chunk_12_15 * chunk_16_19))) * ((chunk_20_23 * (chunk_24_27 * chunk_28_31)) * (chunk_32_35 * (chunk_36_39 * chunk_40_40))))

theorem literal_product_unit : IsUnit literal_product := by
  exact IsUnit.mul (IsUnit.mul (IsUnit.mul (chunk_00_03_unit) (chunk_04_07_unit)) (IsUnit.mul (chunk_08_11_unit) (IsUnit.mul (chunk_12_15_unit) (chunk_16_19_unit)))) (IsUnit.mul (IsUnit.mul (chunk_20_23_unit) (IsUnit.mul (chunk_24_27_unit) (chunk_28_31_unit))) (IsUnit.mul (chunk_32_35_unit) (IsUnit.mul (chunk_36_39_unit) (chunk_40_40_unit))))
#print axioms literal_product_unit

end
end AspisV8R19.R762LiteralBlockProduct

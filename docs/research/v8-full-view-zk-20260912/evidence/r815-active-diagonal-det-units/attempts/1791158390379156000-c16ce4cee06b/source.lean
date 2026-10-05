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
import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R807SourceBlock02Binding
import AspisV8R19.R807SourceBlock03Binding
import AspisV8R19.R807SourceBlock04Binding
import AspisV8R19.R807SourceBlock05Binding
import AspisV8R19.R807SourceBlock07Binding
import AspisV8R19.R807SourceBlock08Binding
import AspisV8R19.R807SourceBlock09Binding
import AspisV8R19.R807SourceBlock10Binding
import AspisV8R19.R807SourceBlock11Binding
import AspisV8R19.R807SourceBlock12Binding
import AspisV8R19.R807SourceBlock13Binding
import AspisV8R19.R807SourceBlock14Binding
import AspisV8R19.R807SourceBlock15Binding
import AspisV8R19.R807SourceBlock16Binding
import AspisV8R19.R807SourceBlock17Binding
import AspisV8R19.R807SourceBlock18Binding
import AspisV8R19.R807SourceBlock19Binding
import AspisV8R19.R807SourceBlock20Binding
import AspisV8R19.R807SourceBlock21Binding
import AspisV8R19.R807SourceBlock22Binding
import AspisV8R19.R807SourceBlock23Binding
import AspisV8R19.R807SourceBlock24Binding
import AspisV8R19.R807SourceBlock25Binding
import AspisV8R19.R807SourceBlock26Binding
import AspisV8R19.R807SourceBlock27Binding
import AspisV8R19.R807SourceBlock28Binding
import AspisV8R19.R807SourceBlock29Binding
import AspisV8R19.R807SourceBlock30Binding
import AspisV8R19.R807SourceBlock31Binding
import AspisV8R19.R807SourceBlock32Binding
import AspisV8R19.R807SourceBlock33Binding
import AspisV8R19.R807SourceBlock34Binding
import AspisV8R19.R807SourceBlock35Binding
import AspisV8R19.R807SourceBlock36Binding
import AspisV8R19.R807SourceBlock37Binding
import AspisV8R19.R807SourceBlock38Binding
import AspisV8R19.R807SourceBlock39Binding
import AspisV8R19.R807SourceBlock40Binding
import AspisV8R19.R815Fin41ExcludeTwo

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R815ActiveDiagonalDetUnits
open AspisV8R19.R807SourceBlock01Binding

theorem active_diagonal_determinants_unit (k : Fin 41) (hk0 : k ≠ (0 : Fin 41)) (hk6 : k ≠ (6 : Fin 41)) :
    IsUnit (diagonalSourceBlock k).det := by
  exact AspisV8R19.R815Fin41ExcludeTwo.fin41_except_two
    (P := fun k : Fin 41 => IsUnit (diagonalSourceBlock k).det)
    (h1 := AspisV8R19.R807SourceBlock01Binding.source_block01_det_unit)
    (h2 := by
      rw [AspisV8R19.R807SourceBlock02Binding.source_block02_eq_certificate]
      exact AspisV8R19.R752SCC02Inverse.determinant_isUnit)
    (h3 := by
      rw [AspisV8R19.R807SourceBlock03Binding.source_block03_eq_certificate]
      exact AspisV8R19.R752SCC03Inverse.determinant_isUnit)
    (h4 := by
      rw [AspisV8R19.R807SourceBlock04Binding.source_block04_eq_certificate]
      exact AspisV8R19.R752SCC04Inverse.determinant_isUnit)
    (h5 := by
      rw [AspisV8R19.R807SourceBlock05Binding.source_block05_eq_certificate]
      exact AspisV8R19.R752SCC05Inverse.determinant_isUnit)
    (h7 := by
      rw [AspisV8R19.R807SourceBlock07Binding.source_block07_eq_certificate]
      exact AspisV8R19.R752SCC07Inverse.determinant_isUnit)
    (h8 := by
      rw [AspisV8R19.R807SourceBlock08Binding.source_block08_eq_certificate]
      exact AspisV8R19.R752SCC08Inverse.determinant_isUnit)
    (h9 := by
      rw [AspisV8R19.R807SourceBlock09Binding.source_block09_eq_certificate]
      exact AspisV8R19.R752SCC09Inverse.determinant_isUnit)
    (h10 := by
      rw [AspisV8R19.R807SourceBlock10Binding.source_block10_eq_certificate]
      exact AspisV8R19.R752SCC10Inverse.determinant_isUnit)
    (h11 := by
      rw [AspisV8R19.R807SourceBlock11Binding.source_block11_eq_certificate]
      exact AspisV8R19.R752SCC11Inverse.determinant_isUnit)
    (h12 := by
      rw [AspisV8R19.R807SourceBlock12Binding.source_block12_eq_certificate]
      exact AspisV8R19.R752SCC12Inverse.determinant_isUnit)
    (h13 := by
      rw [AspisV8R19.R807SourceBlock13Binding.source_block13_eq_certificate]
      exact AspisV8R19.R752SCC13Inverse.determinant_isUnit)
    (h14 := by
      rw [AspisV8R19.R807SourceBlock14Binding.source_block14_eq_certificate]
      exact AspisV8R19.R752SCC14Inverse.determinant_isUnit)
    (h15 := by
      rw [AspisV8R19.R807SourceBlock15Binding.source_block15_eq_certificate]
      exact AspisV8R19.R752SCC15Inverse.determinant_isUnit)
    (h16 := by
      rw [AspisV8R19.R807SourceBlock16Binding.source_block16_eq_certificate]
      exact AspisV8R19.R752SCC16Inverse.determinant_isUnit)
    (h17 := by
      rw [AspisV8R19.R807SourceBlock17Binding.source_block17_eq_certificate]
      exact AspisV8R19.R752SCC17Inverse.determinant_isUnit)
    (h18 := by
      rw [AspisV8R19.R807SourceBlock18Binding.source_block18_eq_certificate]
      exact AspisV8R19.R752SCC18Inverse.determinant_isUnit)
    (h19 := by
      rw [AspisV8R19.R807SourceBlock19Binding.source_block19_eq_certificate]
      exact AspisV8R19.R752SCC19Inverse.determinant_isUnit)
    (h20 := by
      rw [AspisV8R19.R807SourceBlock20Binding.source_block20_eq_certificate]
      exact AspisV8R19.R752SCC20Inverse.determinant_isUnit)
    (h21 := by
      rw [AspisV8R19.R807SourceBlock21Binding.source_block21_eq_certificate]
      exact AspisV8R19.R752SCC21Inverse.determinant_isUnit)
    (h22 := by
      rw [AspisV8R19.R807SourceBlock22Binding.source_block22_eq_certificate]
      exact AspisV8R19.R752SCC22Inverse.determinant_isUnit)
    (h23 := by
      rw [AspisV8R19.R807SourceBlock23Binding.source_block23_eq_certificate]
      exact AspisV8R19.R752SCC23Inverse.determinant_isUnit)
    (h24 := by
      rw [AspisV8R19.R807SourceBlock24Binding.source_block24_eq_certificate]
      exact AspisV8R19.R752SCC24Inverse.determinant_isUnit)
    (h25 := by
      rw [AspisV8R19.R807SourceBlock25Binding.source_block25_eq_certificate]
      exact AspisV8R19.R752SCC25Inverse.determinant_isUnit)
    (h26 := by
      rw [AspisV8R19.R807SourceBlock26Binding.source_block26_eq_certificate]
      exact AspisV8R19.R752SCC26Inverse.determinant_isUnit)
    (h27 := by
      rw [AspisV8R19.R807SourceBlock27Binding.source_block27_eq_certificate]
      exact AspisV8R19.R752SCC27Inverse.determinant_isUnit)
    (h28 := by
      rw [AspisV8R19.R807SourceBlock28Binding.source_block28_eq_certificate]
      exact AspisV8R19.R752SCC28Inverse.determinant_isUnit)
    (h29 := by
      rw [AspisV8R19.R807SourceBlock29Binding.source_block29_eq_certificate]
      exact AspisV8R19.R752SCC29Inverse.determinant_isUnit)
    (h30 := by
      rw [AspisV8R19.R807SourceBlock30Binding.source_block30_eq_certificate]
      exact AspisV8R19.R752SCC30Inverse.determinant_isUnit)
    (h31 := by
      rw [AspisV8R19.R807SourceBlock31Binding.source_block31_eq_certificate]
      exact AspisV8R19.R752SCC31Inverse.determinant_isUnit)
    (h32 := by
      rw [AspisV8R19.R807SourceBlock32Binding.source_block32_eq_certificate]
      exact AspisV8R19.R752SCC32Inverse.determinant_isUnit)
    (h33 := by
      rw [AspisV8R19.R807SourceBlock33Binding.source_block33_eq_certificate]
      exact AspisV8R19.R752SCC33Inverse.determinant_isUnit)
    (h34 := by
      rw [AspisV8R19.R807SourceBlock34Binding.source_block34_eq_certificate]
      exact AspisV8R19.R752SCC34Inverse.determinant_isUnit)
    (h35 := by
      rw [AspisV8R19.R807SourceBlock35Binding.source_block35_eq_certificate]
      exact AspisV8R19.R752SCC35Inverse.determinant_isUnit)
    (h36 := by
      rw [AspisV8R19.R807SourceBlock36Binding.source_block36_eq_certificate]
      exact AspisV8R19.R752SCC36Inverse.determinant_isUnit)
    (h37 := by
      rw [AspisV8R19.R807SourceBlock37Binding.source_block37_eq_certificate]
      exact AspisV8R19.R752SCC37Inverse.determinant_isUnit)
    (h38 := by
      rw [AspisV8R19.R807SourceBlock38Binding.source_block38_eq_certificate]
      exact AspisV8R19.R752SCC38Inverse.determinant_isUnit)
    (h39 := by
      rw [AspisV8R19.R807SourceBlock39Binding.source_block39_eq_certificate]
      exact AspisV8R19.R752SCC39Inverse.determinant_isUnit)
    (h40 := by
      rw [AspisV8R19.R807SourceBlock40Binding.source_block40_eq_certificate]
      exact AspisV8R19.R752SCC40Inverse.determinant_isUnit)
    k hk0 hk6
#print axioms active_diagonal_determinants_unit
end AspisV8R19.R815ActiveDiagonalDetUnits

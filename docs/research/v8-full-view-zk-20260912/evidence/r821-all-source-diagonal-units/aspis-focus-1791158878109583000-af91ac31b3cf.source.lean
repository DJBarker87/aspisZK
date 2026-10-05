import AspisV8R19.R815ActiveDiagonalDetUnits
import AspisV8R19.R819BlockZeroBinding
import AspisV8R19.R812BlockSixBinding
import AspisV8R19.R751JointBlock39Inverse

set_option autoImplicit false
namespace AspisV8R19.R821AllSourceDiagonalUnits
open AspisV8R19.R807SourceBlock01Binding

theorem source_block06_det_unit : IsUnit (diagonalSourceBlock 6).det := by
  rw [R812BlockSixBinding.source_block06_eq_certificate]
  exact isUnit_iff_ne_zero.mpr R751JointBlock39Inverse.determinant_nonzero

theorem all_source_diagonal_units (k : Fin 41) : IsUnit (diagonalSourceBlock k).det := by
  by_cases h0 : k = 0
  · subst k
    exact R819BlockZeroBinding.diagonal_source_block00_det_isUnit
  by_cases h6 : k = 6
  · subst k
    exact source_block06_det_unit
  exact R815ActiveDiagonalDetUnits.active_diagonal_determinants_unit k h0 h6

#print axioms source_block06_det_unit
#print axioms all_source_diagonal_units
end AspisV8R19.R821AllSourceDiagonalUnits

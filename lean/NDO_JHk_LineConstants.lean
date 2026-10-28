import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_CircleNumbers
set_option autoImplicit false
namespace AspisR1.JHk_LineConstants
abbrev FP := Port5Q1_QueryPorts.FP
abbrev FE := AspisWideTower.WideExact
theorem half : (2 : FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
end AspisR1.JHk_LineConstants

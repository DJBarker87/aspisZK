import JFv_TX2_Query0Inverse
import JFw_TX2_CircleNumbers
set_option autoImplicit false
namespace AspisR1.JHk_LineConstants
abbrev FP := Port5Q1_QueryPorts.FP
abbrev FE := AspisWideTower.WideExact
theorem half : (2 : FE)⁻¹=1073741824 := by
  have h := congrArg (algebraMap FP FE)
    (JFv_TX2_Query0Inverse.reciprocal 2 1073741824 (by decide))
  have two : algebraMap FP FE (2 : FP)=(2 : FE) := map_natCast _ _
  have value : algebraMap FP FE (1073741824 : FP)=(1073741824 : FE) := map_natCast _ _
  rw [map_inv₀,two,value] at h
  exact h
#print axioms half
end AspisR1.JHk_LineConstants

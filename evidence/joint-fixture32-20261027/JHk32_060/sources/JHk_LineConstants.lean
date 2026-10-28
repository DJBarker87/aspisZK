import JFv_TX2_Query0Inverse
import JFw_TX2_CircleNumbers
set_option autoImplicit false
namespace AspisR1.JHk_LineConstants
abbrev FP := Port5Q1_QueryPorts.FP
abbrev FE := AspisWideTower.WideExact
theorem half : (2 : FE)⁻¹=1073741824 := by
  have h := congrArg (algebraMap FP FE)
    (JFv_TX2_Query0Inverse.reciprocal 2 1073741824 (by decide))
  simpa only [map_inv₀,map_natCast,Nat.cast_ofNat] using h
#print axioms half
end AspisR1.JHk_LineConstants

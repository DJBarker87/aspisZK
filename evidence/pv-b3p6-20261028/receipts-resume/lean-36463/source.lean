import PV_B3P_Offset226V3
namespace PV_B3P_NestedOffset226V3
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem sub_sub_value (i c d : Usize) (h : c.val + d.val ≤ i.val) :
    (Usize.wrapping_sub (Usize.wrapping_sub i c) d).val = i.val - c.val - d.val := by
  have hc := PV_B3P_Offset226V3.sub_value i c (by omega)
  rw [PV_B3P_Offset226V3.sub_value _ d (by rw [hc]; omega),hc]

#print axioms sub_sub_value
end PV_B3P_NestedOffset226V3

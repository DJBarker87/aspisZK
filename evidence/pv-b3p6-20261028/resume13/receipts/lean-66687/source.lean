import PV_B3P_ProjectedCompute13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
/-- The actual group 0: four reads from succ_z/internal, and leading/full slot. -/
theorem projected_group_bounds13_0 (offset : Usize) (h : offset.val < 4) :
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize 0#usize) offset).val < 16 ∧
    (0#usize).val < 4 := by
  have hm : Usize.wrapping_mul 4#usize 0#usize = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    have hb : (0#usize).val < UScalar.size .Usize := by
      simpa only [UScalar.size] using (0#usize).hBounds
    change ((4 : Nat)*0) % UScalar.size .Usize = 0
    exact Nat.mod_eq_of_lt hb
  rw [hm]
  have hb : (16#usize).val < UScalar.size .Usize := by simpa only [UScalar.size] using (16#usize).hBounds
  have ha := PV_B3P_Offset226V3.add_value 0#usize offset (by change 0+offset.val < UScalar.size .Usize; change 16 < UScalar.size .Usize at hb; omega)
  rw [ha]
  constructor
  · change 0+offset.val < 16
    omega
  · change 0 < 4
    omega
#print axioms projected_group_bounds13_0
end PV_B3P_Binding13227

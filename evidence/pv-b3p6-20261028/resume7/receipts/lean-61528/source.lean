import Aeneas.Std
namespace PV_B3P_Offset226V3
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem sub_value (i c : Usize) (h : c.val ≤ i.val) :
    (Usize.wrapping_sub i c).val = i.val - c.val := by
  rw [Usize.wrapping_sub_val_eq]
  have hi : i.val < UScalar.size .Usize := by
    simpa only [UScalar.size] using i.hBounds
  have hc : c.val < UScalar.size .Usize := by
    simpa only [UScalar.size] using c.hBounds
  have he : i.val + (UScalar.size .Usize - c.val) =
      (i.val - c.val) + UScalar.size .Usize := by omega
  rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem add_value (i c : Usize) (h : i.val + c.val < UScalar.size .Usize) :
    (Usize.wrapping_add i c).val = i.val + c.val := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt h]

#print axioms sub_value
#print axioms add_value
end PV_B3P_Offset226V3

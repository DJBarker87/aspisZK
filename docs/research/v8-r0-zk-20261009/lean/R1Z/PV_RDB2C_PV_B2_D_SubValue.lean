import R1Z.PV_RDB2C_PV_B2_D_SmallScalar
set_option autoImplicit false
namespace PV_B2_D_SubValue
open Aeneas Aeneas.Std

theorem sub_val (a b : Usize) (h : b.val ≤ a.val) :
    (Usize.wrapping_sub a b).val = a.val - b.val := by
  have ha : a.val < UScalar.size .Usize := by simpa only [UScalar.size] using a.hBounds
  have hb : b.val < UScalar.size .Usize := by simpa only [UScalar.size] using b.hBounds
  rw [Usize.wrapping_sub_val_eq]
  rw [show a.val + (UScalar.size .Usize - b.val) = a.val-b.val+UScalar.size .Usize from by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) ha)
#print axioms sub_val
end PV_B2_D_SubValue

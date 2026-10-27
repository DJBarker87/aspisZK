import R1Z.PV_CB_EncoderCell
set_option autoImplicit false
namespace R1Z.PV_CB_EncoderFoldBounds
open Aeneas Aeneas.Std

theorem basis (j : Usize) (inside : j.val<512) : j.val<(512#usize).val := inside
theorem even (j : Usize) (inside : j.val<512) :
    (Usize.wrapping_mul 2#usize j).val<(1024#usize).val := by
  rw [Usize.wrapping_mul_val_eq]
  change (2*j.val)%UScalar.size .Usize<1024
  exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
theorem odd (j : Usize) (inside : j.val<512) :
    (Usize.wrapping_add (Usize.wrapping_mul 2#usize j) 1#usize).val<(1024#usize).val := by
  rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq]
  change ((2*j.val)%UScalar.size .Usize+1)%UScalar.size .Usize<1024
  have a := Nat.mod_le (2*j.val) (UScalar.size .Usize)
  have b := Nat.mod_le ((2*j.val)%UScalar.size .Usize+1) (UScalar.size .Usize)
  omega
#print axioms basis
#print axioms even
#print axioms odd
end R1Z.PV_CB_EncoderFoldBounds

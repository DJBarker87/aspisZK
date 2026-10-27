import PV_B1_MaskCast
set_option autoImplicit false
namespace PV_B1_MaskShift
open Aeneas Aeneas.Std Result

theorem four_mod : 4 % UScalarTy.numBits .Usize = 4 := by
  rcases System.Platform.numBits_eq with h|h <;>
    simp only [UScalarTy.numBits,h]

theorem block_value (row : Usize) :
    (Usize.wrapping_shr row 4#u32).val = row.val / 16 := by
  change (row.bv.ushiftRight (4 % UScalarTy.numBits .Usize)).toNat = _
  rw [four_mod]
  change row.val >>> 4 = row.val / 16
  rw [Nat.shiftRight_eq_div_pow]

theorem in_bounds (row : Usize) :
    (Usize.wrapping_shr row 4#u32).val < 64 ↔ row.val < 1024 := by
  rw [block_value]
  omega

theorem out_of_bounds (row : Usize) (h : 1024 ≤ row.val) :
    64 ≤ (Usize.wrapping_shr row 4#u32).val := by
  rw [block_value]
  omega

theorem bit_value (row : Usize) :
    (U16.wrapping_shl 1#u16 (UScalar.cast .U32 (PV_B1_MaskCast.low row))).val =
      2^(PV_B1_MaskCast.low row).val := by
  change ((1#u16).bv.shiftLeft ((UScalar.cast .U32 (PV_B1_MaskCast.low row)).val % 16)).toNat = _
  rw [PV_B1_MaskCast.cast_value,Nat.mod_eq_of_lt (PV_B1_MaskCast.low_bound row)]
  change (1 <<< (PV_B1_MaskCast.low row).val) % 2^16 = _
  rw [Nat.shiftLeft_eq]
  have hp : 2^(PV_B1_MaskCast.low row).val < 2^16 :=
    Nat.pow_lt_pow_right (by decide) (PV_B1_MaskCast.low_bound row)
  simpa only [Nat.one_mul,Nat.mod_eq_of_lt hp]
#print axioms four_mod
#print axioms block_value
#print axioms in_bounds
#print axioms out_of_bounds
#print axioms bit_value
theorem row_shift_nonfailure (row : Usize) :
    (lift (Usize.wrapping_shr row 4#u32) : Result Usize) =
      .ok (Usize.wrapping_shr row 4#u32) := rfl

theorem bit_shift_nonfailure (row : Usize) :
    (lift (U16.wrapping_shl 1#u16 (UScalar.cast .U32 (PV_B1_MaskCast.low row))) : Result U16) =
      .ok (U16.wrapping_shl 1#u16 (UScalar.cast .U32 (PV_B1_MaskCast.low row))) := rfl
#print axioms row_shift_nonfailure
#print axioms bit_shift_nonfailure
end PV_B1_MaskShift

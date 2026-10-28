import R1Z.PV_B2_D_SmallScalar
set_option autoImplicit false
namespace PV_B2_D_ShiftValue
open Aeneas Aeneas.Std
theorem shift_val (x : Usize) (b : U32) (hb : b.val < 32) :
    (Usize.wrapping_shl x b).val = (x.val * 2^b.val) % UScalar.size .Usize := by
  unfold Usize.wrapping_shl UScalar.wrapping_shl
  simp only [UScalar.val,BitVec.shiftLeft,Nat.shiftLeft_eq,UScalar.size]
  have h : b.val < UScalarTy.Usize.numBits := lt_of_lt_of_le hb System.Platform.le_numBits
  change (x.val <<< (b.val % UScalarTy.Usize.numBits)) % 2^UScalarTy.Usize.numBits = _
  rw [Nat.mod_eq_of_lt h,Nat.shiftLeft_eq]
#print axioms shift_val
end PV_B2_D_ShiftValue

import R1Z.PV_RDB2C_PV_B2_D_SmallScalar
set_option autoImplicit false
namespace PV_B2_D_ShiftValue
open Aeneas Aeneas.Std
theorem shift_val (x : Usize) (b : U32) (hb : b.val < 32) :
    (Usize.wrapping_shl x b).val = (x.val * 2^b.val) % UScalar.size .Usize := by
  unfold Usize.wrapping_shl UScalar.wrapping_shl
  simp only [UScalar.val,BitVec.shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,UScalar.size]
  have h : b.val < UScalarTy.Usize.numBits := lt_of_lt_of_le hb System.Platform.le_numBits
  have h1 : b.bv.toNat < UScalarTy.Usize.numBits := by simpa only [UScalar.val] using h
  rw [Nat.mod_eq_of_lt h1]
#print axioms shift_val
end PV_B2_D_ShiftValue

import NCJ_CallLog
set_option autoImplicit false
namespace NCJ_ShiftTwo
open Aeneas Aeneas.Std

theorem value (x : Usize) : (Usize.wrapping_shr x 2#u32).val=x.val/4 := by
  have bits : 2< UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  change (x.bv >>> ((2#u32).val % UScalarTy.Usize.numBits)).toNat=x.bv.toNat/4
  rw [show (2#u32).val=2 from by decide,Nat.mod_eq_of_lt bits,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

#print axioms value
end NCJ_ShiftTwo

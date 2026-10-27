import RPu_FJf_InstalledPointCell
set_option autoImplicit false
namespace AspisR1.FJf_CommonIndices
open Aeneas Aeneas.Std Result

theorem low (j : Usize) : (j &&& 3#usize).val=j.val%4 := by
  rw [UScalar.val_and]
  change j.val &&& 3=j.val%4
  exact Nat.and_two_pow_sub_one_eq_mod j.val 2


theorem high (j : Usize) : (Usize.wrapping_shr j 2#u32).val=j.val/4 := by
  have bits : 2 < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  change (j.bv >>> ((2#u32).val % UScalarTy.Usize.numBits)).toNat=j.bv.toNat/4
  rw [show (2#u32).val=2 from by decide,Nat.mod_eq_of_lt bits,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
#print axioms low
#print axioms high
end AspisR1.FJf_CommonIndices

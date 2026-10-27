import FJf_InstalledPointCell
set_option autoImplicit false
namespace AspisR1.FJf_CommonIndices
open Aeneas Aeneas.Std Result

theorem low (j : Usize) : (j &&& 3#usize).val=j.val%4 := by
  rw [UScalar.val_and]
  change j.val &&& 3=j.val%4
  exact Nat.and_two_pow_sub_one_eq_mod j.val 2

#print Aeneas.Std.UScalar.wrapping_shr

theorem high (j : Usize) : (Usize.wrapping_shr j 2#u32).val=j.val/4 := by
  change (j.bv >>> (2:Nat)).toNat=j.bv.toNat/4
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
#print axioms low
#print axioms high
end AspisR1.FJf_CommonIndices

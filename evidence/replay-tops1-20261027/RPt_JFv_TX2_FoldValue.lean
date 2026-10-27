import RPt_JFs_TX2_FoldLane
set_option autoImplicit false
namespace AspisR1.JFv_TX2_FoldValue
open Aeneas Aeneas.Std

def value (n : Nat) : Nat := n%2147483648+n/2147483648

theorem low (x : U64) : (x &&& 2147483647#u64).val=x.val%2147483648 := by
  change (x.bv &&& (2147483647 : BitVec 64)).toNat=x.val%2147483648
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.val 31

theorem source (x : U64) : (FIo_ReduceBounds.fold x).val=value x.val := by
  unfold FIo_ReduceBounds.fold U64.wrapping_add
  rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound x),
    low,FIo_ReduceBounds.shr_val]
  rfl

#print axioms low
#print axioms source
end AspisR1.JFv_TX2_FoldValue

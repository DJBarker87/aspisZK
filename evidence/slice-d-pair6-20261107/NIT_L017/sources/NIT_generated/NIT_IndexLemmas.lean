import NIT_PairComposition
set_option autoImplicit false
namespace AspisR1.NIT_IndexLemmas
open Aeneas Aeneas.Std Result

theorem mask (j : Usize) : (j &&& 3#usize).val=j.val%4 := by
 rw [UScalar.val_and]
 exact Nat.and_two_pow_sub_one_eq_mod j.val 2

#check UScalar.wrapping_shr_bv_eq
#check BitVec.toNat_ushiftRight
#print UScalar.wrapping_shr

#print axioms mask
end AspisR1.NIT_IndexLemmas

import FIw_SelectorIndices
set_option autoImplicit false
namespace AspisR1.FIy_FrontierBits
open Aeneas Aeneas.Std Result WP

theorem low (index : U64) : (index &&& 1#u64).val=index.val%2 := by
  rw [UScalar.val_and]
  change index.val &&& 1=index.val%2
  exact Nat.and_two_pow_sub_one_eq_mod index.val 1
#print axioms low
#print UScalar.ShiftRight_UScalar_spec
end AspisR1.FIy_FrontierBits

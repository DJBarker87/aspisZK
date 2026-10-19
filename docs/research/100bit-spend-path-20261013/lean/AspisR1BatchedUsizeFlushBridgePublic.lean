import Aeneas.Std
import Init.Data.Nat.Bitwise.Lemmas

set_option autoImplicit false
open Aeneas.Std

namespace AspisR1BatchedUsizeFlushBridgePublic

abbrev Usize := UScalar UScalarTy.Usize
theorem source_usize_flush_test_iff (terms : Usize) :
    (UScalar.and terms (3#usize)).val = 3 ↔ terms.val % 4 = 3 := by
  let three : Usize := 3#usize
  have hAnd : (UScalar.and terms three).val = terms.val &&& three.val :=
    UScalar.val_and terms three
  rw [hAnd]
  have hthree : three.val = 3 := rfl
  have hAndMod : terms.val &&& 3 = terms.val % 4 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod terms.val 2
  rw [hthree, hAndMod]

#print axioms source_usize_flush_test_iff

end AspisR1BatchedUsizeFlushBridgePublic

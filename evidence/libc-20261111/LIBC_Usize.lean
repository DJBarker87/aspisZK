import Aeneas
set_option autoImplicit false
namespace LIBC_Usize
open Aeneas Aeneas.Std
def raw (n : Nat) : Usize := if h : n ≤ Usize.max then UScalar.ofNat n h else 0#usize
theorem raw_val (n : Nat) (h : n ≤ Usize.max) : (raw n).val = n := by
 unfold raw
 rw [dif_pos h]
 rfl
theorem from_native (n : Usize) : raw n.val = n := by
 apply UScalar.eq_of_val_eq
 exact raw_val n.val (by scalar_tac)
#print axioms raw_val
#print axioms from_native
end LIBC_Usize

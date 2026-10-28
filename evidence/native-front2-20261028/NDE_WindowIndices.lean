import NDE_PublicWindows
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_WindowIndices

theorem digest_index (j : Usize) (h : j.val < 8) : (j &&& 7#usize) = j := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change (j.val &&& 7) = j.val
  calc
    _ = j.val % 8 := Nat.and_two_pow_sub_one_eq_mod j.val 3
    _ = j.val := Nat.mod_eq_of_lt h

theorem digest_window_admitted (j : Usize) (h : j.val < 8) : j.val < 32 := by omega

#print axioms digest_index
#print axioms digest_window_admitted
end NDE_WindowIndices

import NMT_345RSLCarriers
set_option autoImplicit false
namespace NMT_R2_WrapAdd
open Aeneas Aeneas.Std

theorem source (a b c : Usize) (sum : a.val + b.val = c.val) :
 Usize.wrapping_add a b = c := by
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_add_val_eq,sum]
 apply Nat.mod_eq_of_lt
 rw [UScalar.size_def]
 scalar_tac
#print axioms source
end NMT_R2_WrapAdd

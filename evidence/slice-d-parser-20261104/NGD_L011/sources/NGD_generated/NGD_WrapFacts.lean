import NGD_SlotRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_WrapFacts
theorem add (x y z : Usize) (eq : x.val + y.val = z.val) :
    UScalar.wrapping_add x y = z := by
  apply UScalar.eq_of_val_eq
  change (Usize.wrapping_add x y).val = z.val
  rw [Usize.wrapping_add_val_eq, eq]
  exact Nat.mod_eq_of_lt (by have h := z.hmax; rw [UScalar.size_def]; scalar_tac)
theorem mul (x y z : Usize) (eq : x.val * y.val = z.val) :
    UScalar.wrapping_mul x y = z := by
  apply UScalar.eq_of_val_eq
  change (Usize.wrapping_mul x y).val = z.val
  rw [Usize.wrapping_mul_val_eq, eq]
  exact Nat.mod_eq_of_lt (by have h := z.hmax; rw [UScalar.size_def]; scalar_tac)
#print axioms add
#print axioms mul
end NGD_WrapFacts

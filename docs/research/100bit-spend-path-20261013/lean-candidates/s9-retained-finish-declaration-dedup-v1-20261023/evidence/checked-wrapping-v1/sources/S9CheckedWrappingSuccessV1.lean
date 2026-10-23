import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckedWrappingSuccessV1

theorem u64_add_success (a b out : U64) (h : (a+b : Result U64) = .ok out) :
    U64.wrapping_add a b = out := by
  have hv : out.val=a.val+b.val := by scalar_tac
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_add_val_eq,←hv,UScalar.size]
  exact Nat.mod_eq_of_lt out.bv.isLt

theorem u64_sub_success (a b out : U64) (h : (a-b : Result U64) = .ok out) :
    U64.wrapping_sub a b = out := by
  have hv : out.val=a.val-b.val := by scalar_tac
  have hb : b.val ≤ a.val := by scalar_tac
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_sub_val_eq]
  scalar_tac

#print axioms u64_add_success
#print axioms u64_sub_success
end AspisR1S9CheckedWrappingSuccessV1

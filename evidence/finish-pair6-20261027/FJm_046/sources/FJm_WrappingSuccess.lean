import FIo_ScalarBridge
set_option autoImplicit false
namespace AspisR1.FJm_WrappingSuccess
open Aeneas Aeneas.Std Result

theorem add (a b z : U64) (h : a+b=ok z) : U64.wrapping_add a b=z := by
  apply UScalar.eq_of_val_eq
  scalar_tac

theorem sub (a b z : U64) (h : a-b=ok z) : U64.wrapping_sub a b=z := by
  apply UScalar.eq_of_val_eq
  scalar_tac

theorem mul (a b z : U64) (h : a*b=ok z) : U64.wrapping_mul a b=z := by
  apply UScalar.eq_of_val_eq
  scalar_tac
#print axioms add
#print axioms sub
#print axioms mul
end AspisR1.FJm_WrappingSuccess

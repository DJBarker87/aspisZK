import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckedMulWrappingSuccessV1
/-- The retained checked model supplies the exact no-overflow fact through
its successful operation; actual release wrapping multiplication is equal. -/
theorem u64_mul_success (a b out : U64) (h : (a*b : Result U64) = .ok out) :
    U64.wrapping_mul a b = out := by
  change UScalar.tryMk .U64 (a.val*b.val) = .ok out at h
  have hs := UScalar.tryMk_eq .U64 (a.val*b.val)
  rw [h] at hs
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_mul_val_eq,←hs.1,UScalar.size]
  exact Nat.mod_eq_of_lt out.bv.isLt
#print axioms u64_mul_success
end AspisR1S9CheckedMulWrappingSuccessV1

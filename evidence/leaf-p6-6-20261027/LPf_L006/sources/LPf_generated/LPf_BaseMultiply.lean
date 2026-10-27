import LPf_CoreReduction
set_option autoImplicit false
namespace AspisR1.LPf_BaseMultiply
open Aeneas Aeneas.Std Result

/-- Full u32 operands, without a canonical-input restriction. -/
theorem product_bound (x y : U32) : x.val * y.val < 18446744073709551616 := by
  have hx : x.val ≤ 4294967295 := by scalar_tac
  have hy : y.val ≤ 4294967295 := by scalar_tac
  have bound := Nat.mul_le_mul hx hy
  omega

theorem word_product (x y : U32) :
    (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)).val = x.val*y.val := by
  rw [U64.wrapping_mul_val_eq]
  have cx : (UScalar.cast .U64 x).val = x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val = y.val := by scalar_tac
  rw [cx, cy]
  apply Nat.mod_eq_of_lt
  simpa only [UScalar.size,UScalarTy.numBits] using product_bound x y

/-- The actual extracted frozen M31 multiplication is total and equals
natural multiplication modulo P. This is a Lean source theorem, not a claim
that the timed-out Kani exact contract passed. -/
theorem source (x y : U32) : ∃ z,
    FIo_Native.aspis_core.field.M31.mul x y = ok z ∧
    z.val = (x.val*y.val) % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z, run, val, canonical⟩ := LPf_CoreReduction.source
    (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y))
  refine ⟨z, ?_, ?_, canonical⟩
  · simp only [FIo_Native.aspis_core.field.M31.mul,lift,bind_tc_ok,run]
  · rw [word_product] at val
    exact val

#print axioms product_bound
#print axioms word_product
#print axioms source
end AspisR1.LPf_BaseMultiply

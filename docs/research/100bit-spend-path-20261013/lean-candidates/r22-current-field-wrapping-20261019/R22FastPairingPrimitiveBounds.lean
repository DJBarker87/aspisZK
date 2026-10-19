import R22CanonicalCM31

/-! Primitive R22 bounds used by the current fast_pairing Q::raw/mul bodies.
Explicit wrapping sums/subtractions already have their declared semantics.
This module covers widened limb products, constant offsets, small multiples
of partial folds, and reducer-fold bounds. It does not extract Q::raw or its
callers and therefore is not a complete fast-pairing refinement. -/
set_option autoImplicit false
namespace AspisR1.R22FastPairingPrimitiveBounds
open Aeneas Aeneas.Std Result
open CheckedWrappingScalarAgreement ExtractedCurrentReducerOps
open R22CanonicalCM31 R22CurrentReducerMul

/-- The actual one-fold expression is bounded on all stored U64 values. -/
theorem wrapping_fold_lt (x : U64) : (wrappingFold x).val < 10737418240 := by
  obtain ⟨z,hz,hv⟩ := ExtractedCurrentReducer.foldExecution_success x
  rw [fold_agrees] at hz
  have he : wrappingFold x = z := Result.ok.inj hz
  rw [he,hv]
  exact AspisV8R17.RawReducer.first_fold_lt x.val x.bv.isLt

/-- Covers the plain `2*u` and `2*v` products in current fast pairing;
indeed every coefficient at most three fits after any U64 partial fold. -/
theorem folded_multiple_agrees (c x : U64) (hc : c.val ≤ 3) :
    UScalar.mul c (wrappingFold x) =
      ok (UScalar.wrapping_mul c (wrappingFold x)) := by
  have hbound : c.val*(wrappingFold x).val < 2^64 := by
    have hf := wrapping_fold_lt x
    have hmul := Nat.mul_le_mul_right (wrappingFold x).val hc
    omega
  obtain ⟨z,hz,_⟩ := mul_success _ _ hbound
  exact (mul_success_agrees _ _ _ hz).1 ▸ hz

/-- Every widened stored U32 product fits, even before using canonicality. -/
theorem widened_product_agrees (x y : U32) :
    UScalar.mul (widen x) (widen y) =
      ok (UScalar.wrapping_mul (widen x) (widen y)) := by
  have hbound : (widen x).val*(widen y).val < 2^64 := by
    simp only [widen,ExtractedCurrentCM31Mul.widen_value]
    have h := Nat.mul_lt_mul_of_lt_of_lt x.bv.isLt y.bv.isLt
    exact h
  obtain ⟨z,hz,_⟩ := mul_success _ _ hbound
  exact (mul_success_agrees _ _ _ hz).1 ▸ hz

/-- The source's `3*P` and `2*PP` constants cannot overflow U64. -/
theorem constant_multiple_agrees (c x : U64)
    (hc : c.val ≤ 3) (hx : x.val ≤ 2147483647^2) :
    UScalar.mul c x = ok (UScalar.wrapping_mul c x) := by
  have hb : c.val*x.val < 2^64 := by
    have h1 := Nat.mul_le_mul_right x.val hc
    have h2 := Nat.mul_le_mul_left 3 hx
    omega
  obtain ⟨z,hz,_⟩ := mul_success _ _ hb
  exact (mul_success_agrees _ _ _ hz).1 ▸ hz

#print axioms wrapping_fold_lt
#print axioms folded_multiple_agrees
#print axioms widened_product_agrees
#print axioms constant_multiple_agrees
end AspisR1.R22FastPairingPrimitiveBounds

import V7CallerCurrentReleaseR26Qm31DotReductionLoop

/-!
# Raw-word bounds for the current QM31 dot product

The short production path accumulates at most four products of canonical M31
words before reducing.  These lemmas make the no-wrap argument explicit and
reusable by each of the nine generated channels.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawArithmetic

open V7CallerCurrentReleaseR26FieldBridge

abbrev M31 := field.M31

def rawM31Product (left right : M31) : Nat := left.val * right.val

theorem canonical_m31_product_lt_two_pow_62
    (left right : M31)
    (leftCanonical : GeneratedCanonicalM31 left)
    (rightCanonical : GeneratedCanonicalM31 right) :
    rawM31Product left right < 2 ^ 62 := by
  unfold rawM31Product GeneratedCanonicalM31
    AspisAeneasCM31Multiplicative.CanonicalRawM31
    AspisAeneasCM31Multiplicative.m31Modulus at *
  have leftBound : left.val < 2 ^ 31 := by omega
  have rightBound : right.val < 2 ^ 31 := by omega
  by_cases rightZero : right.val = 0
  · simp [rightZero]
  · have first := Nat.mul_lt_mul_of_pos_right leftBound
      (Nat.pos_of_ne_zero rightZero)
    have second := Nat.mul_lt_mul_of_pos_left rightBound
      (by norm_num : 0 < 2 ^ 31)
    norm_num at first second ⊢
    exact lt_trans first second

/-- Four canonical products fit strictly below the U64 modulus. -/
theorem four_canonical_m31_products_fit_u64
    (left0 right0 left1 right1 left2 right2 left3 right3 : M31)
    (left0Canonical : GeneratedCanonicalM31 left0)
    (right0Canonical : GeneratedCanonicalM31 right0)
    (left1Canonical : GeneratedCanonicalM31 left1)
    (right1Canonical : GeneratedCanonicalM31 right1)
    (left2Canonical : GeneratedCanonicalM31 left2)
    (right2Canonical : GeneratedCanonicalM31 right2)
    (left3Canonical : GeneratedCanonicalM31 left3)
    (right3Canonical : GeneratedCanonicalM31 right3) :
    rawM31Product left0 right0 + rawM31Product left1 right1 +
        rawM31Product left2 right2 + rawM31Product left3 right3 < 2 ^ 64 := by
  have bound0 := canonical_m31_product_lt_two_pow_62 left0 right0
    left0Canonical right0Canonical
  have bound1 := canonical_m31_product_lt_two_pow_62 left1 right1
    left1Canonical right1Canonical
  have bound2 := canonical_m31_product_lt_two_pow_62 left2 right2
    left2Canonical right2Canonical
  have bound3 := canonical_m31_product_lt_two_pow_62 left3 right3
    left3Canonical right3Canonical
  norm_num at bound0 bound1 bound2 bound3 ⊢
  omega

theorem cast_u32_u64_val (value : Std.U32) :
    (UScalar.cast .U64 value).val = value.val := by
  simp

theorem wrapping_product_exact
    (left right : M31)
    (leftCanonical : GeneratedCanonicalM31 left)
    (rightCanonical : GeneratedCanonicalM31 right) :
    (Std.U64.wrapping_mul (UScalar.cast .U64 left)
      (UScalar.cast .U64 right)).val = rawM31Product left right := by
  rw [Std.U64.wrapping_mul_val_eq, cast_u32_u64_val,
    cast_u32_u64_val]
  rw [AspisAeneasM31ReduceU64.u64_size_eq]
  apply Nat.mod_eq_of_lt
  exact canonical_m31_product_lt_two_pow_62 left right
    leftCanonical rightCanonical |>.trans (by norm_num)

/-- One generated raw-channel `wrapping_add` is ordinary addition whenever
the caller supplies the chunk-level U64 bound. -/
theorem wrapping_accumulate_exact
    (current : Std.U64) (left right : M31)
    (leftCanonical : GeneratedCanonicalM31 left)
    (rightCanonical : GeneratedCanonicalM31 right)
    (bound : current.val + rawM31Product left right < 2 ^ 64) :
    (Std.U64.wrapping_add current
      (Std.U64.wrapping_mul (UScalar.cast .U64 left)
        (UScalar.cast .U64 right))).val =
      current.val + rawM31Product left right := by
  rw [Std.U64.wrapping_add_val_eq,
    wrapping_product_exact left right leftCanonical rightCanonical]
  rw [AspisAeneasM31ReduceU64.u64_size_eq]
  exact Nat.mod_eq_of_lt (by
    simpa [AspisAeneasM31ReduceU64.u64Cardinality] using bound)

#print axioms canonical_m31_product_lt_two_pow_62
#print axioms four_canonical_m31_products_fit_u64
#print axioms wrapping_accumulate_exact

end V7CallerCurrentReleaseR26Qm31DotRawArithmetic

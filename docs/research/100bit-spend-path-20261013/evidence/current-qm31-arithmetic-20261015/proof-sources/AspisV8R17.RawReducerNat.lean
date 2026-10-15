module
public import Init.Data.Nat.Bitwise.Lemmas
public import Mathlib.Data.Nat.Notation
import Lean.Elab.Tactic.Omega

/-! Natural-number definitions and bounds split from RawReducer. The retained
statements and reducer definitions are unchanged; closed numeral proofs use
`decide` instead of importing the field-algebra tactic stack. -/
set_option autoImplicit false
@[expose] public section
namespace AspisV8R17.RawReducer
abbrev P : ℕ := 2147483647
def CanonicalRawM31 (x : ℕ) : Prop := x<P
def rawM31Add (x y : ℕ) : ℕ := if P≤x+y then x+y-P else x+y

def foldBits (x : Nat) : Nat := (x &&& P) + (x >>> 31)

/-- The same fold expressed by `Nat` division/modulo by `2^31`. -/
def fold31 (x : Nat) : Nat := x % 2 ^ 31 + x / 2 ^ 31

/-- The Rust `as u32` narrowing of a `Nat`, i.e. reduction modulo `2^32`
(`rawWordCount`). -/
def truncU32 (x : Nat) : Nat := x % 2 ^ 32

/-- One conditional subtraction of `P` (`if x >= P then x - P else x`). -/
def condSubP (x : Nat) : Nat := if P ≤ x then x - P else x

/-- The literal `reduce_u64` graph: two bit-folds, an `as u32` truncation, then
one conditional subtraction. -/
def rawReduceU64 (x : Nat) : Nat := condSubP (truncU32 (foldBits (foldBits x)))

/-- `M31::mul` on stored words: reduce the full `u64` product. -/
def rawM31Mul (x y : Nat) : Nat := rawReduceU64 (x * y)

/-! ## The two bitwise identities, proved structurally

Both are general in the bit width and are established from the bitwise
characterisations that ground `&&&`, `2^k - 1` and `% 2^k` in `Nat`
division/modulo.  No specific numeral is tested. -/

/-- Masking off the low `k` bits (AND with `2^k - 1`) is reduction modulo `2^k`.
Proved by `Nat.eq_of_testBit_eq`: bit `i` of each side is `testBit x i`
restricted to `i < k`. -/
theorem mask_low_eq_mod (x k : Nat) : x &&& (2 ^ k - 1) = x % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Bool.and_comm]

/-- Shifting right by `k` is integer division by `2^k`. -/
theorem shift_high_eq_div (x k : Nat) : x >>> k = x / 2 ^ k :=
  Nat.shiftRight_eq_div_pow x k

/-- The literal bit-fold equals the div/mod fold.  Here the low-bit mask is the
Mersenne constant `P = 2^31 - 1`, so `mask_low_eq_mod` applies at `k = 31`. -/
theorem foldBits_eq_fold31 (x : Nat) : foldBits x = fold31 x := by
  unfold foldBits fold31
  rw [show P = 2 ^ 31 - 1 from by decide, mask_low_eq_mod, shift_high_eq_div]

/-! ## Width fits after each fold (task item 1)

Exact bounds used, for every `x < 2^64`:
* after fold 1, `foldBits x < 2^33 + 2^31 = 10737418240` (about 34 bits — it
  stays in `u64`, and is genuinely wider than `u32`, see the load-bearing tooth);
* after fold 2, `foldBits (foldBits x) ≤ 2147483651 = P + 4 < 2^32`, so the
  `as u32` narrowing is exact. -/

/-- Fold 1 keeps any `u64` below `2^33 + 2^31`. -/
theorem first_fold_lt (x : Nat) (hx : x < 2 ^ 64) : foldBits x < 10737418240 := by
  rw [foldBits_eq_fold31]
  unfold fold31
  have hdm := Nat.div_add_mod x (2 ^ 31)
  have hmod : x % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt x (by decide)
  have hdiv : x / 2 ^ 31 < 2 ^ 33 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)]; omega
  have e31 : (2 : Nat) ^ 31 = 2147483648 := by decide
  have e33 : (2 : Nat) ^ 33 = 8589934592 := by decide
  omega

/-- A single fold of anything below `2^33 + 2^31` lands at or below `P + 4`. -/
theorem fold31_second_le (n : Nat) (hn : n < 10737418240) : fold31 n ≤ 2147483651 := by
  unfold fold31
  have hdm := Nat.div_add_mod n (2 ^ 31)
  have hmod : n % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt n (by decide)
  have e31 : (2 : Nat) ^ 31 = 2147483648 := by decide
  omega

/-- After two folds the value is at most `P + 4 = 2147483651`. -/
theorem second_fold_le (x : Nat) (hx : x < 2 ^ 64) :
    foldBits (foldBits x) ≤ 2147483651 := by
  rw [foldBits_eq_fold31, foldBits_eq_fold31]
  exact fold31_second_le (fold31 x) (by rw [← foldBits_eq_fold31]; exact first_fold_lt x hx)

/-- After two folds the value is below `2^32`, so the `as u32` cast is exact. -/
theorem second_fold_lt_two_pow32 (x : Nat) (hx : x < 2 ^ 64) :
    foldBits (foldBits x) < 2 ^ 32 := by
  have h := second_fold_le x hx
  have e : (2 : Nat) ^ 32 = 4294967296 := by decide
  omega

/-- The `as u32` narrowing of the twice-folded value is the identity. -/
theorem second_fold_cast_exact (x : Nat) (hx : x < 2 ^ 64) :
    truncU32 (foldBits (foldBits x)) = foldBits (foldBits x) :=
  Nat.mod_eq_of_lt (second_fold_lt_two_pow32 x hx)

/-! ## One conditional subtraction suffices (task item 2) -/

/-- After two folds the value is below `2 * P`, so a single subtraction of `P`
canonicalises it. -/
theorem second_fold_lt_two_mul_P (x : Nat) (hx : x < 2 ^ 64) :
    foldBits (foldBits x) < 2 * P := by
  have h := second_fold_le x hx
  have hP : P = 2147483647 := rfl
  omega

/-! ## Canonical output (task item 3) -/

/-- `rawReduceU64 x` is canonical for every `u64` input.  The two folds bring
`x` below `2^32` (cast exact) and below `2 * P`, so the single conditional
subtraction lands strictly below `P`. -/
theorem rawReduceU64_canonical (x : Nat) (hx : x < 2 ^ 64) : rawReduceU64 x < P := by
  unfold rawReduceU64 condSubP
  rw [second_fold_cast_exact x hx]
  have hb := second_fold_le x hx
  have hP : P = 2147483647 := rfl
  split <;> omega


theorem fold31_mod (n : Nat) : fold31 n % P = n % P := by
  unfold fold31 P
  have split := Nat.div_add_mod n (2^31)
  omega

theorem rawReduceU64_eq_mod_nat (x : Nat) (hx : x < 2^64) :
    rawReduceU64 x = x % P := by
  have hmod : rawReduceU64 x % P = x % P := by
    unfold rawReduceU64
    rw [second_fold_cast_exact x hx, foldBits_eq_fold31, foldBits_eq_fold31]
    unfold condSubP
    split
    · rename_i h
      rw [← Nat.mod_eq_sub_mod h, fold31_mod, fold31_mod]
    · rw [fold31_mod, fold31_mod]
  rw [Nat.mod_eq_of_lt (rawReduceU64_canonical x hx)] at hmod
  exact hmod

#print axioms first_fold_lt
#print axioms second_fold_cast_exact
#print axioms rawReduceU64_canonical
#print axioms rawReduceU64_eq_mod_nat
end AspisV8R17.RawReducer

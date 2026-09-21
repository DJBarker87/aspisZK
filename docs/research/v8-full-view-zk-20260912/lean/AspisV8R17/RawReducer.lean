import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Narrow replay of retained raw reducer/addition proofs. Declaration bodies
from V5M31RawMulReduction lines 55–232 and QM31RustFormulaSeam lines 160–193
are retained; only imports, namespace and the minimal local aliases change.
This avoids loading the deployment/sampler aggregate for a local arithmetic
delta. It is not a new assertion of extracted Rust equality. -/
set_option autoImplicit false
namespace AspisV8R17.RawReducer
abbrev P : ℕ := 2147483647
abbrev M31Exact := ZMod P
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
  rw [show P = 2 ^ 31 - 1 from by norm_num [P], mask_low_eq_mod, shift_high_eq_div]

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
  have hmod : x % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt x (by norm_num)
  have hdiv : x / 2 ^ 31 < 2 ^ 33 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 31)]; omega
  have e31 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
  have e33 : (2 : Nat) ^ 33 = 8589934592 := by norm_num
  omega

/-- A single fold of anything below `2^33 + 2^31` lands at or below `P + 4`. -/
theorem fold31_second_le (n : Nat) (hn : n < 10737418240) : fold31 n ≤ 2147483651 := by
  unfold fold31
  have hdm := Nat.div_add_mod n (2 ^ 31)
  have hmod : n % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt n (by norm_num)
  have e31 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
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
  have e : (2 : Nat) ^ 32 = 4294967296 := by norm_num
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

/-! ## Residue preservation (task item 4) -/

/-- `2^31` is `1` in the field, because `2^31 = P + 1`. -/
theorem cast_two_pow31 : ((2 ^ 31 : Nat) : M31Exact) = 1 := by
  rw [show (2 ^ 31 : Nat) = P + 1 from by norm_num [P], Nat.cast_add, Nat.cast_one,
    ZMod.natCast_self, zero_add]

/-- One fold preserves the residue class modulo `P`: writing
`n = 2^31 * (n / 2^31) + n % 2^31` and using `2^31 = 1` in the field collapses
the high part onto the low part. -/
theorem fold31_residue (n : Nat) : ((fold31 n : Nat) : M31Exact) = (n : M31Exact) := by
  have hsplit := Nat.div_add_mod n (2 ^ 31)
  unfold fold31
  rw [Nat.cast_add]
  conv_rhs => rw [← hsplit]
  rw [Nat.cast_add, Nat.cast_mul, cast_two_pow31]
  ring

/-- The whole reducer preserves the residue class: the `as u32` cast is exact,
each fold preserves residues, and subtracting `P` in the high branch is a
no-op modulo `P`. -/
theorem rawReduceU64_residue (x : Nat) (hx : x < 2 ^ 64) :
    ((rawReduceU64 x : Nat) : M31Exact) = (x : M31Exact) := by
  unfold rawReduceU64 condSubP
  rw [second_fold_cast_exact x hx, foldBits_eq_fold31, foldBits_eq_fold31]
  have hcond : ((if P ≤ fold31 (fold31 x) then fold31 (fold31 x) - P
      else fold31 (fold31 x) : Nat) : M31Exact) = ((fold31 (fold31 x) : Nat) : M31Exact) := by
    split
    · rename_i h; rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero]
    · rfl
  rw [hcond, fold31_residue, fold31_residue]

/-- Consequently, on `u64` inputs the reducer is exactly the remainder modulo
`P`: canonical output plus preserved residue pins the value uniquely. -/
theorem rawReduceU64_eq_mod (z : Nat) (hz : z < 2 ^ 64) : rawReduceU64 z = z % P := by
  have hcanon : rawReduceU64 z < P := rawReduceU64_canonical z hz
  have hres := rawReduceU64_residue z hz
  rw [ZMod.natCast_eq_natCast_iff] at hres
  have hmodeq : rawReduceU64 z % P = z % P := hres
  rw [Nat.mod_eq_of_lt hcanon] at hmodeq
  exact hmodeq

/-! ## Multiplication seam (task items 5–8) -/

/-- Two canonical M31 factors multiply without overflowing `u64`
(`(P-1)^2 < 2^64`), which is exactly the precondition of the reducer above. -/
theorem canonicalMul_lt_two_pow64 {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) : x * y < 2 ^ 64 := by
  unfold CanonicalRawM31 at hx hy
  have h : x * y ≤ (P - 1) * (P - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (P - 1) * (P - 1) < 2 ^ 64 := by norm_num [P]
  omega

/-- The raw product reducer output is canonical for canonical inputs. -/
theorem rawM31Mul_canonical {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) : CanonicalRawM31 (rawM31Mul x y) :=
  rawReduceU64_canonical _ (canonicalMul_lt_two_pow64 hx hy)

/-- The `ZMod P` image of the raw product equals the product of the input
residues. -/
theorem rawM31Mul_residue {x y : Nat}
    (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    ((rawM31Mul x y : Nat) : M31Exact) = (x : M31Exact) * (y : M31Exact) := by
  unfold rawM31Mul
  rw [rawReduceU64_residue _ (canonicalMul_lt_two_pow64 hx hy), Nat.cast_mul]


theorem rawM31Add_canonical
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    CanonicalRawM31 (rawM31Add x y) := by
  unfold CanonicalRawM31 at hx hy ⊢
  unfold rawM31Add
  by_cases hhigh : P ≤ x + y
  · simp [hhigh]
    omega
  · simp [hhigh]
    omega

/-- The one-subtraction graph is the ordinary remainder because the canonical
input bounds make the unreduced sum strictly smaller than `2*P`. -/
theorem rawM31Add_eq_mod
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    rawM31Add x y = (x + y) % P := by
  by_cases hhigh : P ≤ x + y
  · have hreduced : x + y - P < P := by
      unfold CanonicalRawM31 at hx hy
      omega
    rw [rawM31Add, if_pos hhigh, Nat.mod_eq_sub_mod hhigh,
      Nat.mod_eq_of_lt hreduced]
  · have hlow : x + y < P := Nat.lt_of_not_ge hhigh
    rw [rawM31Add, if_neg hhigh, Nat.mod_eq_of_lt hlow]

/-- The literal Rust addition graph commutes with reduction into the exact
`ZMod (2^31-1)` model.  Both comparison branches are covered explicitly. -/
theorem residue_rawM31Add
    {x y : Nat} (_hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) :
    ((rawM31Add x y : Nat) : M31Exact) =
      (x : M31Exact) + (y : M31Exact) := by
  by_cases hhigh : P ≤ x + y
  · rw [rawM31Add, if_pos hhigh, Nat.cast_sub hhigh, Nat.cast_add,
      ZMod.natCast_self, sub_zero]
  · rw [rawM31Add, if_neg hhigh, Nat.cast_add]


#print axioms rawReduceU64_canonical
#print axioms rawReduceU64_residue
#print axioms rawM31Mul_residue
#print axioms residue_rawM31Add
end AspisV8R17.RawReducer


import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! D59.2 / D62.3 / D64.2 (hRound, hGRound): the `K` model of the Rust pure-round
columns, in a light module (Mathlib only), in the style of `CertRelK`.

The checker's QPrime and G round columns are the Z4c coordinates of the balanced
sources of z9.rs `Lanes::bal` (z9.rs:1001-1027): lane `c < 10` (mask-only), lane 10
(G, scaled by the tower basis element `k`) built from probe.rs:262-337 `round_row`,
and lane 11 (D, scaled likewise) built from probe.rs:2256-2278 `tail_row`.  The
definitions below follow those loops literally:

* `pcR b w e d` is the `for _ in 0..e` loop of `round_row` (`t[d] += p[d]·b`,
  `t[d+1] += p[d]·w[j]`), i.e. coefficient `d` of `(b + w X)^e` (`pcR_eq`);
* `pgR` adds the G constant (`p[0] += 1` when `c = 10`);
* `fullR` is the `full` loop (multiplication by `X` when the row bit is 1, by
  `1 - X` when it is 0);
* `rrowR A i u c r p` is entry `p` of `round_row(a, r, c)` (`out[0]` the
  initial sum, `out[1 + 27j]` = `full[0]`, `out[1 + 27j + k]` = `full[k + 1]`);
* `trowR A co p` is entry `p` of `tail_row` at transported coefficient `co`;
* `srcRoundR` is the balanced source of `Lanes::bal`: raw row `r` minus, for a
  copy-inactive `r` (`Fl r = 1`), raw row 0.

`A` are the ten alpha challenges, `i, u` the tower generators, `T` the transport
table and `Fl` the inactive flags, as in `CertRelK`.  Nothing here is evaluated. -/

set_option autoImplicit false

namespace R1Z.CertRound

open scoped BigOperators
open Polynomial

variable {K : Type} [Field K]

/-- probe.rs:13 `EXP`. -/
def expR (c : ℕ) : ℕ := [1, 3, 5, 7, 9, 11, 15, 17, 19, 21].getD c 0

/-- `round_row` family. -/
def famR (c : ℕ) : ℕ := if c = 10 then 16 else 0

/-- `round_row` exponent. -/
def exR (c : ℕ) : ℕ := if c = 10 then 26 else expR c

/-- probe.rs `tower(k)`: `1, i, u, iu`. -/
def tbR (i u : K) (k : ℕ) : K :=
  if k = 0 then 1 else if k = 1 then i else if k = 2 then u else if k = 3 then i * u else 0

/-- `round_row` rotation. -/
def rotR (i u : K) (c : ℕ) : K := if c = 10 then 1 else tbR i u (c % 4)

/-- `round_row` weight `w[i]`. -/
def wR (fam i : ℕ) : K := ((3 + 22 * i + fam * (17 + 8 * i) : ℕ) : K)

/-- `r >> (9 - i) & 1 == 1`. -/
def bitR (r i : ℕ) : Bool := r.testBit (9 - i)

/-- `b` of round `j`: `Σ_{i<j} a_i w_i + Σ_{i>j, bit i} w_i`. -/
def bR (A : ℕ → K) (fam j r : ℕ) : K :=
  (∑ i ∈ Finset.range j, A i * wR fam i) +
    ∑ i ∈ Finset.range 10, if j < i ∧ bitR r i = true then wR fam i else 0

/-- `pref` before round `j`. -/
def prefR (A : ℕ → K) (j r : ℕ) : K :=
  ∏ i ∈ Finset.range j, if bitR r i = true then A i else 1 - A i

/-- `boolean`: the weighted bit sum of row `r`. -/
def boolR (fam r : ℕ) : K := ∑ i ∈ Finset.range 10, if bitR r i = true then wR fam i else 0

/-- Coefficients of `(b + w X)^e` by the Rust loop. -/
def pcR (b w : K) : ℕ → ℕ → K
  | 0, d => if d = 0 then 1 else 0
  | e + 1, d => pcR b w e d * b + (if d = 0 then 0 else pcR b w e (d - 1) * w)

/-- `p` after the G constant. -/
def pgR (c : ℕ) (b w : K) (d : ℕ) : K := pcR b w (exR c) d + (if c = 10 ∧ d = 0 then 1 else 0)

/-- `full`: `v·X` (bit 1) or `v·(1 - X)` (bit 0). -/
def fullR (bit : Bool) (v : ℕ → K) (d : ℕ) : K :=
  if bit = true then (if d = 0 then 0 else v (d - 1)) else v d - (if d = 0 then 0 else v (d - 1))

/-- The round coefficient stored at Z4c entry `k` (`out.push(full[0])`, `out.extend(&full[2..])`). -/
def coeffR (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

/-- Entry `p` of `round_row(a, r, c)` (lanes `c ≤ 10`). -/
def rrowR (A : ℕ → K) (i u : K) (c r p : ℕ) : K :=
  if p = 0 then rotR i u c * boolR (famR c) r ^ exR c + (if c = 10 then 1 else 0)
  else fullR (bitR r ((p - 1) / 27))
    (fun d => pgR c (bR A (famR c) ((p - 1) / 27) r) (wR (famR c) ((p - 1) / 27)) d *
      prefR A ((p - 1) / 27) r * rotR i u c) (coeffR ((p - 1) % 27))

/-- `tail_row`'s `m`: the Libra variable of coefficient `co`. -/
def mR (co : ℕ) : ℕ := if co < 28 then 8 else 9

/-- `tail_row` entry `1 + 27j + k` (`j < 10`, `k < 27`) at coefficient `co < 56`
(`d = co % 28`, `endpoint_sum = 2` if `d = 0` else `1`). -/
def tcellR (A : ℕ → K) (co j k : ℕ) : K :=
  if j < mR co then
    (if k = 0 then (if co % 28 = 0 then 2 else 1) * ((2 ^ (8 - j) : ℕ) : K) else 0)
  else if j = mR co then
    (if co % 28 ≠ 1 ∧ k = (if co % 28 = 0 then 0 else co % 28 - 1) then ((2 ^ (9 - j) : ℕ) : K) else 0)
  else (if k = 0 then A (mR co) ^ (co % 28) * ((2 ^ (9 - j) : ℕ) : K) else 0)

/-- Entry `p` of `tail_row` at transported coefficient `co` (zero for `co ≥ 56`). -/
def trowR (A : ℕ → K) (co p : ℕ) : K :=
  if 56 ≤ co then 0
  else if p = 0 then (if co % 28 = 0 then 2 else 1) * 512
  else if 10 ≤ (p - 1) / 27 then 0
  else tcellR A co ((p - 1) / 27) ((p - 1) % 27)

/-- Entry `p` of the balanced source (lane `c`, row `r`, limb `k`) of `Lanes::bal`. -/
def srcRoundR (A : ℕ → K) (T : ℕ → ℕ) (Fl : ℕ → K) (i u : K) (c r k p : ℕ) : K :=
  if c < 10 then rrowR A i u c r p - Fl r * rrowR A i u c 0 p
  else if c = 10 then tbR i u k * (rrowR A i u 10 r p - Fl r * rrowR A i u 10 0 p)
  else tbR i u k * (trowR A (T r) p - Fl r * trowR A (T 0) p)

/-! ### Generic lemmas -/

/-- The Rust power loop computes the coefficients of `(C w * X + C b)^e`. -/
theorem pcR_eq (b w : K) : ∀ e d, pcR b w e d = ((C w * X + C b) ^ e).coeff d := by
  intro e
  induction e with
  | zero =>
    intro d
    rw [pcR, pow_zero, coeff_one]
  | succ e ih =>
    intro d
    have h : (C w * X + C b : K[X]) ^ (e + 1) =
        (C w * X + C b) ^ e * X * C w + (C w * X + C b) ^ e * C b := by ring
    rw [pcR, h, coeff_add, coeff_mul_C, coeff_mul_C]
    cases d with
    | zero =>
      rw [if_pos rfl, coeff_mul_X_zero, ← ih 0]
      ring
    | succ d =>
      rw [if_neg (show d + 1 ≠ 0 by omega), coeff_mul_X, ← ih d, ← ih (d + 1), Nat.add_sub_cancel]
      ring

/-- Multiplication by `X` or `1 - X` on coefficients is `fullR`. -/
theorem coeff_bitMul (bit : Bool) (Q : K[X]) (d : ℕ) :
    ((if bit = true then X else 1 - X) * Q).coeff d = fullR bit (fun n => Q.coeff n) d := by
  unfold fullR
  cases bit with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    cases d with
    | zero => rw [coeff_X_mul_zero, if_pos rfl]
    | succ d => rw [coeff_X_mul, if_neg (show d + 1 ≠ 0 by omega), Nat.add_sub_cancel]
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, sub_mul, one_mul, coeff_sub]
    cases d with
    | zero => rw [coeff_X_mul_zero, if_pos rfl]
    | succ d => rw [coeff_X_mul, if_neg (show d + 1 ≠ 0 by omega), Nat.add_sub_cancel]

theorem fullR_mul (bit : Bool) (v : ℕ → K) (c : K) (d : ℕ) :
    fullR bit (fun n => v n * c) d = fullR bit v d * c := by
  unfold fullR
  split_ifs <;> ring

theorem fullR_congr (bit : Bool) (v v' : ℕ → K) (h : ∀ n, v n = v' n) (d : ℕ) :
    fullR bit v d = fullR bit v' d := by
  unfold fullR
  simp only [h]

#print axioms pcR_eq
#print axioms coeff_bitMul
#print axioms fullR_mul
#print axioms fullR_congr

end R1Z.CertRound

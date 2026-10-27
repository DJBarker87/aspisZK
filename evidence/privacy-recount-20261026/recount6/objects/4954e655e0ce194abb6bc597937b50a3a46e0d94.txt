import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! J0c numeral (LOG D40.3, D42.1): the pole term of `privacy_R1` at the cap
N = 8, `N · (4096 / Q) ≤ 2^-108` whenever `Q ≥ 2^123`, and `p⁴ ≥ 2^123` for
the M31 prime `p = 2^31 − 1` (`AspisCircleGroupOrder.P` is the abbreviation
`2 ^ 31 - 1`), so for `Q = p⁴ = |QM31|` the pole term is at most 2^-108.
No large numeral is evaluated: `p⁴ ≥ 2^123` is the polynomial inequality
`8·(4+y)⁴ ≤ (2y+7)⁴` at `2^30 = 4 + y`, and the ℚ bound is a monotonicity step
plus `2^123 = 2^15 · 2^108`.  This module imports only the tactics it uses. -/
set_option autoImplicit false

namespace R1Z.PoleN8

/-- `p⁴ ≥ 2^123` for `p = 2^31 − 1`. -/
theorem m31_pow4 : 2 ^ 123 ≤ (2 ^ 31 - 1) ^ 4 := by
  have h31 : (2 : ℕ) ^ 31 = 2 * 2 ^ 30 := by norm_num
  have h123 : (2 : ℕ) ^ 123 = 2 ^ 3 * (2 ^ 30) ^ 4 := by
    rw [← pow_mul, ← pow_add]
  have h4 : (4 : ℕ) ≤ 2 ^ 30 := by norm_num
  rw [h31, h123]
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le h4
  rw [hy, show 2 * (4 + y) - 1 = 2 * y + 7 by omega,
    show (2 * y + 7) ^ 4 = 2 ^ 3 * (4 + y) ^ 4 +
      (8 * y ^ 4 + 96 * y ^ 3 + 408 * y ^ 2 + 696 * y + 353) by ring]
  exact Nat.le_add_right _ _

/-- The pole term of `privacy_R1` at N = 8 for any `Q ≥ 2^123`. -/
theorem pole_N8 (Q : ℕ) (hQ : 2 ^ 123 ≤ Q) :
    ((8 : ℕ) : ℚ) * ((4096 : ℚ) / Q) ≤ 1 / 2 ^ 108 := by
  have hQ' : (2 : ℚ) ^ 123 ≤ Q := by exact_mod_cast hQ
  have hpos : (0 : ℚ) < 2 ^ 123 := by positivity
  have h1 : ((8 : ℕ) : ℚ) * ((4096 : ℚ) / Q) = 2 ^ 15 / Q := by
    push_cast
    ring
  rw [h1]
  calc (2 : ℚ) ^ 15 / Q ≤ 2 ^ 15 / 2 ^ 123 := div_le_div_of_nonneg_left (by positivity) hpos hQ'
    _ = 1 / 2 ^ 108 := by
      rw [show (123 : ℕ) = 15 + 108 from rfl, pow_add, div_mul_eq_div_div,
        div_self (by positivity)]

/-- The instantiation `Q = p⁴`, `p = 2^31 − 1`: `8 · 4096 / p⁴ ≤ 2^-108`. -/
theorem pole_N8_M31 :
    ((8 : ℕ) : ℚ) * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 : ℕ) : ℚ)) ≤ 1 / 2 ^ 108 :=
  pole_N8 _ m31_pow4

#print axioms m31_pow4
#print axioms pole_N8
#print axioms pole_N8_M31
end R1Z.PoleN8

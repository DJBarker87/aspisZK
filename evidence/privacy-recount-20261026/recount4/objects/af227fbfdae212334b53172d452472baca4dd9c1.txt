import R1Z.QueryScanFreshUnion

set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanFreshNumerics
open R1Z.QueryScanFreshUnion R1Z.QueryScanRealLazyBound R1Z.QueryScanRealEntropy

/-- Monotonicity in the total prior-query envelope. -/
theorem fresh_budget_mono {q r : ℕ} (hq : q ≤ r) : freshBudget q ≤ freshBudget r := by
  unfold freshBudget
  gcongr

theorem fresh_budget_pow65 : freshBudget (2^65) = 1 / (2 : ℚ)^118 := by
  unfold freshBudget
  rw [Nat.cast_pow, Nat.cast_ofNat, show (190 : ℕ) = 65 + 125 from rfl, pow_add]
  have h128 : (128 : ℚ) = 2^7 := by norm_num
  rw [h128, show (125 : ℕ) = 7 + 118 from rfl, pow_add]
  field_simp

theorem fresh_budget_small {q : ℕ} (hq : q ≤ 2^65) :
    freshBudget q ≤ 1 / (2 : ℚ)^109 := by
  exact (fresh_budget_mono hq).trans (fresh_budget_pow65.le.trans
    (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 118)))

/-- The single conservative coupling budget fits inside the same numerical
freshness allowance. This is an inequality of budgets, not equality of events. -/
theorem lazy_budget_le_fresh {M q : ℕ} (hM : M ≤ 2^25) (hq : 1 ≤ q) :
    lazyBudget M ≤ freshBudget q := by
  apply (lazy_budget_sharp hM).trans
  apply (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 190 ≤ 204)).trans
  have h1 : 1 / (2 : ℚ)^190 ≤ freshBudget 1 := by
    unfold freshBudget
    rw [Nat.cast_one, mul_one]
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℚ) ≤ 128) (by positivity)
  exact h1.trans (fresh_budget_mono hq)

theorem fresh_total_lt_target {q : ℕ} (hq : q ≤ 2^65) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + freshBudget q <
      1 / (2 : ℚ)^100 :=
  QueryScanHistoryRealNumerics.total_lt_target _ (fresh_budget_small hq)

/-- Keep the large dyadic denominator opaque to ring preprocessing. -/
theorem amount_identity (a κ d : ℚ) :
    ((κ + 8 / d) + a) + 8 / d = a + 16 / d + κ := by ring

#print axioms fresh_budget_mono
#print axioms fresh_budget_pow65
#print axioms fresh_budget_small
#print axioms lazy_budget_le_fresh
#print axioms fresh_total_lt_target
#print axioms amount_identity
end R1Z.QueryScanFreshNumerics

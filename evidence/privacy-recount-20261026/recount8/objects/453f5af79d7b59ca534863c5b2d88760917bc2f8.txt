import R1Z.QueryScanWholeRunRepeatReal

/-! Independent numerical facts, not an assertion of a real-run collision law
or of a run-budget theorem. Six is the existing five-reader-plus-output
collision coefficient. The run would still have to prove the stated q cap. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanHistoryRealNumerics

def kappa (q : ℕ) : ℚ := 6 * (q : ℚ)^2 / (2 : ℚ)^256

theorem kappa_mono {q r : ℕ} (hq : q ≤ r) : kappa q ≤ kappa r := by
  unfold kappa
  gcongr

/-- Closed form only: no evaluation of 2^256 or a recurrence. -/
theorem kappa_pow (b d : ℕ) (h : b * 2 + d = 256) :
    kappa (2^b) = 6 / (2 : ℚ)^d := by
  unfold kappa
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← h, pow_add]
  field_simp

/-- Inverse powers decrease with the exponent. -/
theorem dyadic_mono {m n : ℕ} (h : m ≤ n) :
    1 / (2 : ℚ)^n ≤ 1 / (2 : ℚ)^m := by
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

/-- A candidate envelope q ≤ 2^65 gives exactly c=6 and ample numerical slack.
This is conditional on a budget, not proof that the whole-run event is rare. -/
theorem kappa_budget {q : ℕ} (hq : q ≤ 2^65) :
    kappa q ≤ 1 / (2 : ℚ)^109 := by
  apply (kappa_mono hq).trans
  rw [kappa_pow 65 126 (by omega)]
  have h6 : (6 : ℚ) ≤ 2^17 := calc
    6 ≤ (2 : ℚ)^3 := by norm_num
    _ ≤ 2^17 := pow_le_pow_right₀ (by norm_num) (by omega)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [show (126 : ℕ) = 109 + 17 by omega, pow_add, one_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right h6
    (le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 2) 109))

/-- The requested numerical conclusion follows by monotonicity and exponent
splitting whenever a genuine collision law supplies this small a term. -/
theorem total_lt_target (κ : ℚ) (hκ : κ ≤ 1 / (2 : ℚ)^109) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + κ <
      1 / (2 : ℚ)^100 := by
  have h137 := dyadic_mono (by omega : 109 ≤ 137)
  have h454 := dyadic_mono (by omega : 109 ≤ 454)
  have hsum : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + κ ≤
      4 / (2 : ℚ)^109 := by
    have h4 (a : ℚ) : a + a + a + a = 4 * a := by ring
    calc
      _ ≤ 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^109 +
          1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^109 :=
        add_le_add (add_le_add (add_le_add
          (le_refl (1 / (2 : ℚ)^109)) h137) h454) hκ
      _ = 4 * (1 / (2 : ℚ)^109) := h4 _
      _ = 4 / (2 : ℚ)^109 := mul_one_div _ _
  apply hsum.trans_lt
  have he : 4 / (2 : ℚ)^109 = 1 / (2 : ℚ)^107 := by
    rw [show (109 : ℕ) = 107 + 2 by omega, pow_add]
    rw [show (2 : ℚ)^2 = 4 by norm_num]
    field_simp
  rw [he]
  exact one_div_lt_one_div_of_lt (by positivity)
    (pow_lt_pow_right₀ (by norm_num) (by omega : 100 < 107))

theorem budget_total_lt_target {q : ℕ} (hq : q ≤ 2^65) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + kappa q <
      1 / (2 : ℚ)^100 := total_lt_target _ (kappa_budget hq)

#print axioms kappa_mono
#print axioms kappa_pow
#print axioms dyadic_mono
#print axioms kappa_budget
#print axioms total_lt_target
#print axioms budget_total_lt_target
end R1Z.QueryScanHistoryRealNumerics

import CantorZassenhausFastTrial
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace AspisR1.CantorZassenhausRetries
open Polynomial AspisR1.CantorZassenhausFastTrial
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The dependency now tests normalized monic gcds. Probability indicator for all independent trials failing, as a product
of their zero/one indicators. -/
def allFail (f : K[X]) (q t : Nat) (tape : Fin t → K×K) : ℚ :=
  ∏ i, fastFailure f q (tape i)

theorem independent_retry_identity (f : K[X]) (q t : Nat) :
    (∑ tape : Fin t → K×K, allFail f q t tape) / (((q : ℚ)^2)^t) =
      ((∑ c : K×K, fastFailure f q c) / ((q : ℚ)^2))^t := by
  unfold allFail
  rw [←Fintype.sum_pow,div_pow]

theorem independent_retry_failure_le (f : K[X]) (a b : K) (q t : Nat)
    (hq : q=Fintype.card K) (hf : f.Monic) (hdeg : (0 : WithBot Nat)<degree f)
    (hab : a≠b) (hodd : ringChar K ≠ 2) (hfa : IsRoot f a) (hfb : IsRoot f b) :
    (∑ tape : Fin t → K×K, allFail f q t tape) / (((q : ℚ)^2)^t) ≤ (1/2)^t := by
  rw [independent_retry_identity]
  have hn : 0 ≤ (∑ c : K×K, fastFailure f q c) / ((q : ℚ)^2) := by
    apply div_nonneg _ (sq_nonneg _)
    apply Finset.sum_nonneg
    intro c _
    unfold fastFailure
    split <;> norm_num
  exact pow_le_pow_left₀ hn (linear_fast_trial_failure_le_half f a b q hq hf hdeg hab hodd hfa hfb) t

/-- Conditional global budget. The caller must separately prove its split-site
count and account for every other randomized/timeout failure. -/
theorem candidate_global_budget (m : Nat) (hm : m ≤ 395412192) :
    (m : ℚ) * (1/2)^149 < 1 / (2 : ℚ)^120 := by
  have hc : (m : ℚ) ≤ 395412192 := by exact_mod_cast hm
  have hbase : (395412192 : ℚ) * (1/2)^149 < 1 / (2 : ℚ)^120 := by norm_num
  have hnonneg : (0 : ℚ) ≤ (1/2)^149 := by positivity
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hnonneg) hbase

#print axioms independent_retry_identity
#print axioms independent_retry_failure_le
#print axioms candidate_global_budget
end AspisR1.CantorZassenhausRetries

import AspisV8Privacy.AdaptiveComposition

/-! A conditional release lower bound gives a stopping tail without IID. The
source-specific lower bound is deliberately not postulated here. -/
set_option autoImplicit false

namespace AspisV8Privacy

theorem bounded_retry_failure (failure : Nat → ℚ) (a : ℚ)
    (atMostOne : a ≤ 1) (initial : failure 0 ≤ 1)
    (step : ∀ n, failure (n + 1) ≤ failure n * (1 - a)) :
    ∀ n, failure n ≤ (1 - a) ^ n := by
  have nonnegative : 0 ≤ 1 - a := sub_nonneg.mpr atMostOne
  intro n
  induction n with
  | zero => simpa using initial
  | succ n ih =>
      calc
        failure (n + 1) ≤ failure n * (1 - a) := step n
        _ ≤ (1 - a) ^ n * (1 - a) := mul_le_mul_of_nonneg_right ih nonnegative
        _ = (1 - a) ^ (n + 1) := (pow_succ (1 - a) n).symm

#print axioms bounded_retry_failure

end AspisV8Privacy

import Std
namespace R1Z.PV_CB3_GammaWrap
set_option autoImplicit false

/-- Folding the high base-power quotient contributes q modulo B-1. -/
theorem fold_high (power low quotient : Nat) (positive : 0 < power) :
    (low + power * quotient) % (power - 1) = (low + quotient) % (power - 1) := by
  have h : power = (power - 1) + 1 := by omega
  have heq : low + power * quotient = (low + quotient) + (power - 1) * quotient := by
    calc
      _ = low + ((power - 1) + 1) * quotient := congrArg (fun n => low + n * quotient) h
      _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
  rw [heq, Nat.add_mul_mod_self_left]

/-- The single wrap and increment used by gamma sampling, before field decoding.
The range hypotheses are internal recurrence invariants, not an output premise. -/
theorem wrap_increment (power low quotient : Nat)
    (power_large : 2 ≤ power) (low_bound : low < power) (quotient_bound : quotient < power - 1) :
    (if low + quotient + 1 < power then low + quotient + 1
      else low + quotient + 2 - power) =
      (low + power * quotient) % (power - 1) + 1 := by
  rw [fold_high power low quotient (by omega)]
  by_cases h : low + quotient + 1 < power
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega : low + quotient < power - 1)]
  · rw [if_neg h]
    have lower : power - 1 ≤ low + quotient := by omega
    have upper : low + quotient - (power - 1) < power - 1 := by omega
    rw [Nat.mod_eq_sub_mod lower, Nat.mod_eq_of_lt upper]
    omega

#print axioms fold_high
#print axioms wrap_increment
end R1Z.PV_CB3_GammaWrap

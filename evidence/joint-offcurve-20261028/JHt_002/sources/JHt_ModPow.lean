import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.JHt_ModPow
/-- One recursive occurrence per bit; all recursive bases are reduced modulo m. -/
def modPow (a e m : Nat) : Nat :=
  if h : e = 0 then 1 % m else
    (a ^ (e % 2) * modPow (a * a % m) (e / 2) m) % m
termination_by e

theorem correct (a e m : Nat) : modPow a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on generalizing a with
  | h e ih =>
    rw [modPow]
    split_ifs with hz
    · simp [hz]
    · rw [ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))]
      have he : e % 2 + 2 * (e / 2) = e := by omega
      rw [← Nat.pow_mod, Nat.mul_mod_mod, ← pow_two, ← pow_mul, ← pow_add, he]
#print axioms correct
end AspisR1.JHt_ModPow

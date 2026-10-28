import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.JHt_BinaryModPow
/-- Structural recursion on a bit budget, with one recursive occurrence.
The zero-budget branch is used only for exponent zero in concrete checks. -/
def modPow (a e m : Nat) : Nat → Nat
  | 0 => 1 % m
  | k + 1 => (a ^ (e % 2) * modPow (a * a % m) (e / 2) m k) % m

theorem correct (a e m k : Nat) (h : e < 2 ^ k) :
    modPow a e m k = a ^ e % m := by
  induction k generalizing a e with
  | zero =>
    have he : e = 0 := by simpa using h
    simp [modPow, he]
  | succ k ih =>
    rw [modPow, ih (a * a % m) (e / 2) (by
      rw [pow_succ] at h
      omega)]
    have he : e % 2 + 2 * (e / 2) = e := by omega
    rw [← Nat.pow_mod, Nat.mul_mod_mod, ← pow_two, ← pow_mul, ← pow_add, he]
#print axioms correct
end AspisR1.JHt_BinaryModPow

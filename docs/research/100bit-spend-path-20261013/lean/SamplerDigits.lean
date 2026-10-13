import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Symbolic base-`p` low-digit arithmetic.  These results do not identify a
Rust implementation, machine-word behavior, or a probability distribution. -/

set_option autoImplicit false

namespace AspisR1.SamplerDigits

/-- The low `n` radix-`p` digits of `x`, defined by repeated quotient/remainder. -/
def lowValue (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % p + p * lowValue p n (x / p)

theorem lowValue_decomposition {p n x : Nat} (hp : 0 < p) :
    x = lowValue p n x + p ^ n * (x / p ^ n) := by
  induction n generalizing x with
  | zero => simp [lowValue]
  | succ n ih =>
      change x = (x % p + p * lowValue p n (x / p)) +
        p ^ (n + 1) * (x / p ^ (n + 1))
      have hdiv := ih (x := x / p)
      have hmod : x = x % p + p * (x / p) := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div x p).symm
      have hquot : (x / p) / p ^ n = x / (p ^ n * p) := by
        simpa [Nat.mul_comm] using (Nat.div_div_eq_div_mul x p (p ^ n))
      rw [hquot] at hdiv
      calc
        x = x % p + p * (x / p) := hmod
        _ = x % p + p * (lowValue p n (x / p) +
              p ^ n * (x / (p ^ n * p))) :=
                congrArg (fun y => x % p + p * y) hdiv
        _ = (x % p + p * lowValue p n (x / p)) +
              p ^ (n + 1) * (x / p ^ (n + 1)) := by
                rw [Nat.pow_succ]
                rw [Nat.mul_comm (p ^ n) p]
                ring

theorem lowValue_lt_pow {p n x : Nat} (hp : 0 < p) :
    lowValue p n x < p ^ n := by
  induction n generalizing x with
  | zero => simp [lowValue]
  | succ n ih =>
      change x % p + p * lowValue p n (x / p) < p ^ (n + 1)
      have hmod : x % p < p := Nat.mod_lt _ hp
      have hlow : lowValue p n (x / p) < p ^ n := ih (x := x / p)
      have hmod' : x % p + 1 ≤ p := Nat.succ_le_of_lt hmod
      have hprod : p * lowValue p n (x / p) + p ≤ p * p ^ n := by
        have h := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hlow)
        rw [Nat.mul_succ] at h
        exact h
      calc
        x % p + p * lowValue p n (x / p) < p * p ^ n := by omega
        _ = p ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem lowValue_eq_mod_pow {p n x : Nat} (hp : 0 < p) :
    lowValue p n x = x % p ^ n := by
  have hdecomp := lowValue_decomposition (p := p) (n := n) (x := x) hp
  have hlow := lowValue_lt_pow (p := p) (n := n) (x := x) hp
  have hmod :
      (lowValue p n x + p ^ n * (x / p ^ n)) % p ^ n = lowValue p n x := by
    rw [Nat.add_mod]
    simp
    exact Nat.mod_eq_of_lt hlow
  calc
    lowValue p n x =
        (lowValue p n x + p ^ n * (x / p ^ n)) % p ^ n := hmod.symm
    _ = x % p ^ n := (congrArg (fun y : Nat => y % p ^ n) hdecomp).symm

#print axioms lowValue_decomposition
#print axioms lowValue_lt_pow
#print axioms lowValue_eq_mod_pow

end AspisR1.SamplerDigits

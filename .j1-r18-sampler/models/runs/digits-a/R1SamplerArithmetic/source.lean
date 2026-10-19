import R1SamplerCarry
import R1SamplerDigits

/-! Composition of the repeated-digit and carry arithmetic models. These
identities do not identify a Rust loop, a fixed-width word, or a byte encoding.
The remaining quotient bound is explicit and is discharged separately for
the 256-bit input and eight M31 digits. -/

set_option autoImplicit false
namespace AspisR1.SamplerArithmetic

open AspisR1.SamplerCarry AspisR1.SamplerDigits

/-- Arithmetic result before decoding the ordinary field tuple. -/
def ordinaryRank (p n x : Nat) : Nat := lowValue p n x

/-- Arithmetic result of adding the remaining quotient and applying the
single end-around carry used by the nonzero sampler. -/
def gammaRank (p n x : Nat) : Nat :=
  carryResult (p ^ n) (x / p ^ n) (lowValue p n x)

theorem ordinaryRank_eq_mod {p n x : Nat} (hp : 0 < p) :
    ordinaryRank p n x = x % p ^ n :=
  lowValue_eq_mod_pow hp

theorem gammaRank_eq_mod {p n x : Nat} (hp : 0 < p)
    (hN : 2 ≤ p ^ n) (hq : x / p ^ n < p ^ n - 1) :
    gammaRank p n x = x % (p ^ n - 1) + 1 ∧
      0 < gammaRank p n x ∧ gammaRank p n x < p ^ n := by
  have hdecomp : (x / p ^ n) * p ^ n + lowValue p n x = x := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (lowValue_decomposition (p := p) (n := n) (x := x) hp).symm
  have h := carry_modular_identity hN hq
    (lowValue_lt_pow (p := p) (n := n) (x := x) hp)
  rw [hdecomp] at h
  exact h

/-- The extra increment in the carry branch cannot wrap again. -/
theorem gammaRank_no_second_wrap {p n x : Nat} (hp : 0 < p)
    (hN : 2 ≤ p ^ n) (hq : x / p ^ n < p ^ n - 1)
    (hwrap : p ^ n ≤ lowValue p n x + x / p ^ n + 1) :
    lowValue p n x + x / p ^ n + 1 - p ^ n + 1 < p ^ n :=
  wrapped_result_lt hN hq (lowValue_lt_pow hp) hwrap

#print axioms ordinaryRank_eq_mod
#print axioms gammaRank_eq_mod
#print axioms gammaRank_no_second_wrap

end AspisR1.SamplerArithmetic

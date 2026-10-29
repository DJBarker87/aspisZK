import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! `Nat.Prime 2147483647` by a Lucas certificate (DESIGN-BUILDER-MODEL §13 (3)).

Witness 7; p - 1 = 2 · 3² · 7 · 11 · 31 · 151 · 331.  Each power
7^((p-1)/q) in ZMod p is reduced by `reduce_mod_char`, which uses Mathlib's
`evalNatPowMod` (binary exponentiation with certified steps, intermediate
values < p²); the seven small primes by norm_num.  No trial division and no
unbounded numeral is evaluated. -/
set_option autoImplicit false

namespace R0Z

theorem m31_prime : Nat.Prime 2147483647 := by
  refine lucas_primality 2147483647 7 ?_ ?_
  · show (7 : ZMod 2147483647) ^ 2147483646 = 1
    reduce_mod_char
  · intro q hq hdvd
    have hfac : 2147483647 - 1 = 2 * 3 * 3 * 7 * 11 * 31 * 151 * 331 := by norm_num
    rw [hfac] at hdvd
    simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 7 by norm_num),
      Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 11 by norm_num),
      Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 31 by norm_num),
      Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 151 by norm_num),
      Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 331 by norm_num)] at hdvd
    rcases hdvd with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
    · show (7 : ZMod 2147483647) ^ 1073741823 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 715827882 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 715827882 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 306783378 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 195225786 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 69273666 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 14221746 ≠ 1
      reduce_mod_char
      decide
    · show (7 : ZMod 2147483647) ^ 6487866 ≠ 1
      reduce_mod_char
      decide

end R0Z

#print axioms R0Z.m31_prime

import R1SamplerAddDigits
import R1SamplerArithmetic

/-! Connect the explicit digit-add recursion to positional modular arithmetic.
This is a Nat algorithm model; no Rust/fixed-width correspondence is asserted. -/
set_option autoImplicit false
namespace AspisR1.SamplerAddBridge
open AspisR1.SamplerAddDigits AspisR1.SamplerCarry

theorem digitsValue_lt_pow {p : Nat} (hp : 0 < p) (digits : List Nat)
    (hcan : ∀ d ∈ digits, d < p) : digitsValue p digits < p ^ digits.length := by
  induction digits with
  | nil => simp [digitsValue]
  | cons d ds ih =>
    have hd : d < p := hcan d (by simp)
    have ht : digitsValue p ds < p ^ ds.length :=
      ih (fun a ha => hcan a (by simp [ha]))
    have hprod := Nat.mul_le_mul_left p (Nat.succ_le_of_lt ht)
    simp only [List.length_cons, digitsValue, pow_succ]
    rw [Nat.mul_succ] at hprod
    rw [Nat.mul_comm (p ^ ds.length) p]
    omega

theorem addDigits_mod_div {p : Nat} (hp : 0 < p) (addend : Nat) (digits : List Nat) :
    digitsValue p (addDigits p addend digits).1 =
        (digitsValue p digits + addend) % p ^ digits.length ∧
      (addDigits p addend digits).2 =
        (digitsValue p digits + addend) / p ^ digits.length := by
  have hb := digitsValue_lt_pow hp (addDigits p addend digits).1
    (addDigits_output_digits_lt p addend digits hp)
  rw [addDigits_length] at hb
  have hv := addDigits_value_conservation p addend digits
  constructor
  · rw [← hv, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hb]
  · rw [← hv, Nat.add_mul_div_left _ _ (Nat.pow_pos hp)]
    simp [Nat.div_eq_of_lt hb]

/-- The source-shaped end-around carry algorithm at the level of lists of
natural-number digits. -/
def endAround (p q : Nat) (digits : List Nat) : List Nat :=
  let first := addDigits p (q + 1) digits
  if first.2 = 0 then first.1 else (addDigits p 1 first.1).1

theorem endAround_value {p q : Nat} (hp : 0 < p) (digits : List Nat)
    (hcan : ∀ d ∈ digits, d < p)
    (hN : 2 ≤ p ^ digits.length) (hq : q < p ^ digits.length - 1) :
    digitsValue p (endAround p q digits) =
      carryResult (p ^ digits.length) q (digitsValue p digits) := by
  let N := p ^ digits.length
  let r := digitsValue p digits
  have hr : r < N := digitsValue_lt_pow hp digits hcan
  have hfirst := addDigits_mod_div hp (q + 1) digits
  have hsecond := addDigits_mod_div hp 1 (addDigits p (q + 1) digits).1
  rw [addDigits_length] at hsecond
  have hsum : r + q + 1 < 2 * N := by dsimp [N] at *; omega
  unfold endAround
  by_cases hs : r + q + 1 < N
  · have hzero : (addDigits p (q + 1) digits).2 = 0 := by
      rw [hfirst.2]
      exact Nat.div_eq_of_lt (by simpa [r, N, Nat.add_assoc] using hs)
    rw [if_pos hzero, hfirst.1]
    change (r + (q + 1)) % N = carryResult N q r
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [carryResult, if_pos hs]
    omega
  · have hge : N ≤ r + q + 1 := by omega
    have hnonzero : (addDigits p (q + 1) digits).2 ≠ 0 := by
      rw [hfirst.2]
      have hpos : 0 < (r + q + 1) / N := Nat.div_pos hge (by dsimp [N]; omega)
      simpa [r, N, Nat.add_assoc] using Nat.ne_of_gt hpos
    rw [if_neg hnonzero, hsecond.1, hfirst.1]
    change ((r + (q + 1)) % N + 1) % N = carryResult N q r
    have hsub : r + (q + 1) - N < N := by omega
    have hmod : (r + (q + 1)) % N = r + (q + 1) - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub]
    rw [hmod]
    have hlast : r + (q + 1) - N + 1 < N := by
      simpa [Nat.add_assoc] using wrapped_result_lt hN hq hr hge
    rw [Nat.mod_eq_of_lt hlast]
    simp only [carryResult, if_neg hs]
    omega

#print axioms digitsValue_lt_pow
#print axioms addDigits_mod_div
#print axioms endAround_value
end AspisR1.SamplerAddBridge

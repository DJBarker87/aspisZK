import R1Z.PV_CB3_SamplerDivision
namespace R1Z.PV_CB3_DigitSequence
open PV_CB3_SamplerCarry (value)
open PV_CB3_SamplerDivision (divideLE)
set_option autoImplicit false

/-- Repeated full-word division, collecting low base digits in source order. -/
def splitDigits (base radix : Nat) : Nat → List Nat → List Nat × List Nat
  | 0, words => ([], words)
  | n + 1, words =>
    let pass := divideLE base radix words
    let rest := splitDigits base radix n pass.1
    (pass.2 :: rest.1, rest.2)

theorem digits_length (base radix n : Nat) (words : List Nat) :
    (splitDigits base radix n words).1.length = n := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih => simp only [splitDigits, List.length_cons, ih]

theorem quotient_length (base radix n : Nat) (words : List Nat) :
    (splitDigits base radix n words).2.length = words.length := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih => simp only [splitDigits, ih, PV_CB3_SamplerDivision.length_preserved]

theorem digits_canonical (base radix : Nat) (positive : 0 < base)
    (n : Nat) (words : List Nat) :
    ∀ d, d ∈ (splitDigits base radix n words).1 → d < base := by
  induction n generalizing words with
  | zero => intro d h; simp only [splitDigits, List.not_mem_nil] at h
  | succ n ih =>
    intro d h
    simp only [splitDigits, List.mem_cons] at h
    rcases h with h | h
    · subst d
      exact PV_CB3_SamplerDivision.remainder_lt base radix positive words
    · exact ih _ d h

/-- The full rank is retained as low digits plus the untruncated high quotient. -/
theorem value_conserved (base radix n : Nat) (words : List Nat) :
    value base (splitDigits base radix n words).1 +
      base ^ n * value radix (splitDigits base radix n words).2 =
      value radix words := by
  induction n generalizing words with
  | zero => simp only [splitDigits, value, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | succ n ih =>
    cases hp : divideLE base radix words with
    | mk quotient remainder =>
      have h := ih quotient
      simp only [splitDigits, hp, value]
      calc
        _ = remainder + base *
            (value base (splitDigits base radix n quotient).1 +
              base ^ n * value radix (splitDigits base radix n quotient).2) := by
          simp only [Nat.pow_succ, Nat.mul_add]
          ac_rfl
        _ = remainder + base * value radix quotient := by rw [h]
        _ = value radix words := by
          have hpv := PV_CB3_SamplerDivision.value_conserved base radix words
          rw [hp] at hpv
          omega

#print axioms digits_length
#print axioms quotient_length
#print axioms digits_canonical
#print axioms value_conserved
end R1Z.PV_CB3_DigitSequence

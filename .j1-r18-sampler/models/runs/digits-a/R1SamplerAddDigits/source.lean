import R1SamplerLongDivision
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Pure Nat model of a little-endian base-p digit carry pass. It does not
model mutation, fixed-width arithmetic, or Rust source operations. -/

set_option autoImplicit false

namespace AspisR1.SamplerAddDigits

/-- Little-endian positional value: the head digit is the least significant. -/
def digitsValue (p : Nat) : List Nat → Nat
  | [] => 0
  | digit :: digits => digit + p * digitsValue p digits

/-- Add an addend to the low-endian digit list, returning the final carry. -/
def addDigits (p addend : Nat) : List Nat → List Nat × Nat
  | [] => ([], addend)
  | digit :: digits =>
      let s := digit + addend
      let (out, carry) := addDigits p (s / p) digits
      (s % p :: out, carry)

theorem addDigits_length (p addend : Nat) (digits : List Nat) :
    (addDigits p addend digits).1.length = digits.length := by
  induction digits generalizing addend with
  | nil => simp [addDigits]
  | cons digit digits ih =>
      simp [addDigits, ih]

theorem addDigits_value_conservation (p addend : Nat) (digits : List Nat) :
    digitsValue p (addDigits p addend digits).1 +
        p ^ digits.length * (addDigits p addend digits).2 =
      digitsValue p digits + addend := by
  induction digits generalizing addend with
  | nil => simp [addDigits, digitsValue]
  | cons digit digits ih =>
      have hih := ih (addend := (digit + addend) / p)
      have hdivision : (digit + addend) % p + p * ((digit + addend) / p) =
          digit + addend := Nat.mod_add_div (digit + addend) p
      simp only [List.length_cons, addDigits, digitsValue]
      calc
        (digit + addend) % p +
              p * digitsValue p (addDigits p ((digit + addend) / p) digits).1 +
              p ^ (digits.length + 1) * (addDigits p ((digit + addend) / p) digits).2
            = (digit + addend) % p + p *
                (digitsValue p (addDigits p ((digit + addend) / p) digits).1 +
                  p ^ digits.length * (addDigits p ((digit + addend) / p) digits).2) := by
                rw [pow_succ]
                ring
        _ = (digit + addend) % p + p *
              (digitsValue p digits + (digit + addend) / p) := by rw [hih]
        _ = p * digitsValue p digits +
              ((digit + addend) % p + p * ((digit + addend) / p)) := by ring
        _ = p * digitsValue p digits + (digit + addend) := by rw [hdivision]
        _ = digitsValue p (digit :: digits) + addend := by
              simp [digitsValue]
              ring

theorem addDigits_output_digits_lt (p addend : Nat) (digits : List Nat)
    (hp : 0 < p) :
    ∀ digit ∈ (addDigits p addend digits).1, digit < p := by
  induction digits generalizing addend with
  | nil => simp [addDigits]
  | cons digit digits ih =>
      intro outputDigit hmem
      simp only [addDigits, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · simpa [hhead] using Nat.mod_lt (digit + addend) hp
      · exact ih (addend := (digit + addend) / p) outputDigit htail

theorem final_carry_le_one_of_addend_le_one {p addend : Nat}
    (hp : 2 ≤ p) (digits : List Nat) (hdigits : ∀ digit ∈ digits, digit < p)
    (haddend : addend ≤ 1) :
    (addDigits p addend digits).2 ≤ 1 := by
  induction digits generalizing addend with
  | nil => simpa [addDigits] using haddend
  | cons digit digits ih =>
      have hdigit : digit < p := hdigits digit (by simp)
      have hsum : digit + addend < 2 * p := by omega
      have hquot : (digit + addend) / p < 2 := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).2
        simpa [Nat.mul_comm] using hsum
      have hquot_le : (digit + addend) / p ≤ 1 := by omega
      have htail : ∀ x ∈ digits, x < p := by
        intro x hx
        exact hdigits x (by simp [hx])
      simpa [addDigits] using ih (addend := (digit + addend) / p) htail hquot_le

theorem final_carry_le_one_nonempty {p addend digit : Nat}
    (hp : 2 ≤ p) (haddend : addend < p) (hdigit : digit < p)
    (digits : List Nat) (hdigits : ∀ x ∈ digits, x < p) :
    (addDigits p addend (digit :: digits)).2 ≤ 1 := by
  have hsum : digit + addend < 2 * p := by omega
  have hquot : (digit + addend) / p < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).2
    simpa [Nat.mul_comm] using hsum
  have hquot_le : (digit + addend) / p ≤ 1 := by omega
  simpa [addDigits] using
    final_carry_le_one_of_addend_le_one hp digits hdigits hquot_le

#print axioms addDigits_length
#print axioms addDigits_value_conservation
#print axioms addDigits_output_digits_lt
#print axioms final_carry_le_one_of_addend_le_one
#print axioms final_carry_le_one_nonempty

end AspisR1.SamplerAddDigits

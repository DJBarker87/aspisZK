import R1SamplerWordPass
import R1SamplerNatModel

/-! Iterate the already checked bounded word-division pass. The returned
remainders are Nat values of the UInt64 machine results. This connects the
word arithmetic model to the existing low-digit model, not to an extracted
Rust loop or its array/index execution. -/
set_option autoImplicit false
namespace AspisR1.SamplerRepeatedPass
open SamplerMachineBounds SamplerWordPass SamplerPass

def wordValue (words : List UInt32) : Nat :=
  numeral B (words.map UInt32.toNat)

def run : Nat → List UInt32 → List Nat × List UInt32
  | 0, words => ([], words)
  | n + 1, words =>
      let step := machineProcess 0 words
      let tail := run n step.2
      (step.1.toNat :: tail.1, tail.2)

private theorem step_facts (words : List UInt32) :
    (machineProcess 0 words).1.toNat = wordValue words % P ∧
      wordValue (machineProcess 0 words).2 = wordValue words / P := by
  have h := machineProcess_correct (0 : UInt64) words (by norm_num [P])
  simpa [wordValue] using h

theorem run_digits (n : Nat) (words : List UInt32) :
    (run n words).1 = SamplerNatModel.lowDigits P n (wordValue words) := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih =>
      simp only [run, SamplerNatModel.lowDigits]
      rw [ih, (step_facts words).1, (step_facts words).2]

theorem run_remaining (n : Nat) (words : List UInt32) :
    wordValue (run n words).2 = wordValue words / P^n := by
  induction n generalizing words with
  | zero => simp [run]
  | succ n ih =>
      simp only [run]
      rw [ih, (step_facts words).2, Nat.div_div_eq_div_mul, pow_succ]
      rw [Nat.mul_comm P (P^n)]

theorem run_digits_value (n : Nat) (words : List UInt32) :
    SamplerAddDigits.digitsValue P (run n words).1 = wordValue words % P^n := by
  rw [run_digits, SamplerNatModel.lowDigits_value,
    SamplerDigits.lowValue_eq_mod_pow P_pos]

theorem run_digits_canonical (n : Nat) (words : List UInt32) :
    ∀ d ∈ (run n words).1, d < P := by
  rw [run_digits]
  exact SamplerNatModel.lowDigits_canonical P_pos n (wordValue words)

#print axioms run_digits
#print axioms run_remaining
#print axioms run_digits_value
#print axioms run_digits_canonical
end AspisR1.SamplerRepeatedPass

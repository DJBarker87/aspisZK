import R1SamplerLongDivision
import Lean.Elab.Tactic.Omega

/-! The long-division state follows the high-to-low numeral fold.  The results
are arithmetic abstractions and do not identify any source implementation. -/

set_option autoImplicit false

namespace AspisR1.SamplerPass

/-- The value of a high-to-low list of radix digits. -/
def numeral (radix : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun a d => a * radix + d) 0

theorem process_processedValue (radix divisor : Nat) (state : AspisR1.SamplerLongDivision.State)
    (digits : List Nat) :
    (AspisR1.SamplerLongDivision.process radix divisor state digits).processedValue =
      digits.foldl (fun a d => a * radix + d) state.processedValue := by
  induction digits generalizing state with
  | nil => rfl
  | cons digit digits ih =>
      simpa [AspisR1.SamplerLongDivision.process,
        AspisR1.SamplerLongDivision.longDivisionStep] using
        (ih (state := AspisR1.SamplerLongDivision.longDivisionStep
          radix divisor state digit))

theorem initialState_process_quotient_remainder
    {radix divisor : Nat} (hradix : 0 < radix) (hdivisor : 0 < divisor)
    (digits : List Nat) (hdigits : ∀ digit ∈ digits, digit < radix) :
    let finalState := AspisR1.SamplerLongDivision.process radix divisor
      AspisR1.SamplerLongDivision.initialState digits
    finalState.quotient = numeral radix digits / divisor ∧
      finalState.remainder = numeral radix digits % divisor := by
  let finalState := AspisR1.SamplerLongDivision.process radix divisor
    AspisR1.SamplerLongDivision.initialState digits
  have hcorrect := AspisR1.SamplerLongDivision.initialState_process_correct
    hradix hdivisor digits hdigits
  have hfold := process_processedValue radix divisor
    AspisR1.SamplerLongDivision.initialState digits
  have hnum : numeral radix digits =
      divisor * finalState.quotient + finalState.remainder := by
    change numeral radix digits = divisor * finalState.quotient + finalState.remainder
    have hpv : finalState.processedValue = numeral radix digits := by
      simpa [finalState, numeral, AspisR1.SamplerLongDivision.initialState] using hfold
    rw [← hpv]
    exact hcorrect.1
  have hrem : finalState.remainder < divisor := hcorrect.2
  have hquotient : numeral radix digits / divisor = finalState.quotient := by
    apply Nat.div_eq_of_lt_le
    · rw [hnum]
      calc
        finalState.quotient * divisor = divisor * finalState.quotient :=
          Nat.mul_comm _ _
        _ ≤ divisor * finalState.quotient + finalState.remainder := Nat.le_add_right _ _
    · rw [hnum]
      calc
        divisor * finalState.quotient + finalState.remainder <
            divisor * finalState.quotient + divisor :=
          Nat.add_lt_add_left hrem _
        _ = (finalState.quotient + 1) * divisor := by
          rw [Nat.add_mul, one_mul, Nat.mul_comm finalState.quotient divisor]
  have hmod : numeral radix digits % divisor = finalState.remainder := by
    have h := Nat.mod_add_div (numeral radix digits) divisor
    rw [hquotient] at h
    conv_rhs at h => rw [hnum]
    rw [Nat.mul_comm divisor finalState.quotient] at h
    omega
  exact ⟨hquotient.symm, hmod.symm⟩

#print axioms process_processedValue
#print axioms initialState_process_quotient_remainder

end AspisR1.SamplerPass

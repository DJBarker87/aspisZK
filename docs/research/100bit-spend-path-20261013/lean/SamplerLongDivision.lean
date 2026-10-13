import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-! Arithmetic facts for a high-to-low base-radix long-division pass.
This file makes no claim about a Rust implementation, fixed-width machine
arithmetic, or a probability distribution. -/

set_option autoImplicit false

namespace AspisR1.SamplerLongDivision

/-- One long-division pass over a single radix digit. -/
def dividend (radix remainder digit : Nat) : Nat := remainder * radix + digit

theorem dividend_lt_mul {radix divisor remainder digit : Nat}
    (hradix : 0 < radix) (hdivisor : 0 < divisor)
    (hremainder : remainder < divisor) (hdigit : digit < radix) :
    dividend radix remainder digit < divisor * radix := by
  dsimp [dividend]
  calc
    remainder * radix + digit < remainder * radix + radix :=
      Nat.add_lt_add_left hdigit _
    _ = (remainder + 1) * radix := by rw [Nat.add_mul, one_mul]
    _ ≤ divisor * radix :=
      Nat.mul_le_mul_right radix (Nat.succ_le_of_lt hremainder)

theorem quotient_lt_radix {radix divisor remainder digit : Nat}
    (hradix : 0 < radix) (hdivisor : 0 < divisor)
    (hremainder : remainder < divisor) (hdigit : digit < radix) :
    dividend radix remainder digit / divisor < radix := by
  apply (Nat.div_lt_iff_lt_mul hdivisor).2
  have h := dividend_lt_mul hradix hdivisor hremainder hdigit
  simpa [dividend, Nat.mul_comm] using h

theorem remainder_lt_divisor {radix divisor remainder digit : Nat}
    (hdivisor : 0 < divisor) :
    dividend radix remainder digit % divisor < divisor :=
  Nat.mod_lt _ hdivisor

theorem dividend_eq_division {radix divisor remainder digit : Nat} :
    dividend radix remainder digit =
      divisor * (dividend radix remainder digit / divisor) +
        dividend radix remainder digit % divisor := by
  dsimp [dividend]
  simpa [Nat.add_comm, Nat.mul_comm] using
    (Nat.mod_add_div (remainder * radix + digit) divisor).symm

/-- Accumulated quotient, current remainder, and the value of the processed
prefix. -/
structure State where
  quotient : Nat
  remainder : Nat
  processedValue : Nat
  deriving Repr, DecidableEq

def initialState : State := ⟨0, 0, 0⟩

/-- Append one digit to the processed prefix and update the quotient/remainder. -/
def longDivisionStep (radix divisor : Nat) (state : State) (digit : Nat) : State :=
  let n := dividend radix state.remainder digit
  ⟨state.quotient * radix + n / divisor,
    n % divisor,
    state.processedValue * radix + digit⟩

theorem step_preserves_invariant {radix divisor : Nat}
    (hradix : 0 < radix) (hdivisor : 0 < divisor)
    (state : State) (digit : Nat)
    (hinvariant : state.processedValue =
      divisor * state.quotient + state.remainder)
    (hremainder : state.remainder < divisor)
    (hdigit : digit < radix) :
    let next := longDivisionStep radix divisor state digit
    next.processedValue = divisor * next.quotient + next.remainder ∧
      next.remainder < divisor := by
  dsimp [longDivisionStep]
  let n := dividend radix state.remainder digit
  have hdivision := dividend_eq_division (radix := radix) (divisor := divisor)
    (remainder := state.remainder) (digit := digit)
  have hdivision' : n = divisor * (n / divisor) + n % divisor := by
    simpa [n] using hdivision
  constructor
  · rw [hinvariant]
    calc
      (divisor * state.quotient + state.remainder) * radix + digit
          = divisor * state.quotient * radix + n := by
              dsimp [n, dividend]
              ring
      _ = divisor * state.quotient * radix +
            (divisor * (n / divisor) + n % divisor) :=
              congrArg (fun x => divisor * state.quotient * radix + x) hdivision'
      _ = divisor * (state.quotient * radix + n / divisor) + n % divisor := by ring
  · exact remainder_lt_divisor (radix := radix) (divisor := divisor)
      (remainder := state.remainder) (digit := digit) hdivisor

/-- Repeatedly process a digit list from its most-significant end. -/
def process (radix divisor : Nat) : State → List Nat → State
  | state, [] => state
  | state, digit :: digits =>
      process radix divisor (longDivisionStep radix divisor state digit) digits

theorem process_preserves_invariant {radix divisor : Nat}
    (hradix : 0 < radix) (hdivisor : 0 < divisor)
    (digits : List Nat) (state : State)
    (hinvariant : state.processedValue =
      divisor * state.quotient + state.remainder)
    (hremainder : state.remainder < divisor)
    (hdigits : ∀ digit ∈ digits, digit < radix) :
    let finalState := process radix divisor state digits
    finalState.processedValue = divisor * finalState.quotient + finalState.remainder ∧
      finalState.remainder < divisor := by
  induction digits generalizing state with
  | nil =>
      simpa [process] using And.intro hinvariant hremainder
  | cons digit digits ih =>
      have hdigit : digit < radix := hdigits digit (by simp)
      have htail : ∀ x ∈ digits, x < radix := by
        intro x hx
        exact hdigits x (by simp [hx])
      have hstep := step_preserves_invariant hradix hdivisor state digit
        hinvariant hremainder hdigit
      simpa [process] using
        ih (state := longDivisionStep radix divisor state digit)
          hstep.1 hstep.2 htail

theorem initialState_process_correct {radix divisor : Nat}
    (hradix : 0 < radix) (hdivisor : 0 < divisor)
    (digits : List Nat) (hdigits : ∀ digit ∈ digits, digit < radix) :
    let finalState := process radix divisor initialState digits
    finalState.processedValue = divisor * finalState.quotient + finalState.remainder ∧
      finalState.remainder < divisor := by
  apply process_preserves_invariant hradix hdivisor digits initialState
  · rfl
  · exact hdivisor
  · exact hdigits

#print axioms dividend_lt_mul
#print axioms quotient_lt_radix
#print axioms dividend_eq_division
#print axioms step_preserves_invariant
#print axioms process_preserves_invariant
#print axioms initialState_process_correct

end AspisR1.SamplerLongDivision

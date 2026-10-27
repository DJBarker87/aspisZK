import R1Z.PDict_EventReplay244
set_option autoImplicit false
namespace R1Z.PDict_OSRegression244
open PDict_EventWorld244

def initial {T Q E A : Type} (entropy : T) (entropyUsed : Nat)
    (request : Q) (error : E) (value : A) : World T Q (Except E A) :=
  ⟨entropy,entropyUsed,[⟨request,.error error⟩,⟨request,.ok value⟩],0⟩

/-- The first OS error is returned and consumes its event; it cannot disappear
behind the exception branch or be re-read by the next caller. -/
theorem first_error {T Q E A : Type} [DecidableEq Q] (entropy : T) (entropyUsed : Nat)
    (request : Q) (error : E) (value : A) :
    step request (initial entropy entropyUsed request error value) =
      some (.error error,{initial entropy entropyUsed request error value with fileUsed := 1}) := by
  simp [step,PDict_TapeCore244.read,tape,initial]

theorem second_success {T Q E A : Type} [DecidableEq Q] (entropy : T) (entropyUsed : Nat)
    (request : Q) (error : E) (value : A) :
    step request {initial entropy entropyUsed request error value with fileUsed := 1} =
      some (.ok value,{initial entropy entropyUsed request error value with fileUsed := 2}) := by
  simp [step,PDict_TapeCore244.read,tape,initial]

theorem error_success_replay {T Q E A : Type} [DecidableEq Q]
    (entropy : T) (entropyUsed : Nat) (request : Q) (error : E) (value : A) :
    Replay (initial entropy entropyUsed request error value)
      [⟨request,.error error⟩,⟨request,.ok value⟩]
      {initial entropy entropyUsed request error value with fileUsed := 2} := by
  exact .cons (first_error entropy entropyUsed request error value)
    (.cons (second_success entropy entropyUsed request error value) (.nil _))

/-- A pure fixed dictionary cannot stand for the preceding two native outcomes
at identical arguments. This is a model obstruction, not a shipped-code attack. -/
theorem no_fixed_outcomes {Q E A : Type} (f : Q → Except E A)
    (request : Q) (error : E) (value : A) :
    ¬ (f request = .error error ∧ f request = .ok value) := by
  intro h
  cases h.1.symm.trans h.2

#print axioms first_error
#print axioms second_success
#print axioms error_success_replay
#print axioms no_fixed_outcomes
end R1Z.PDict_OSRegression244

import FSOracleExecution

/-!
IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. Requires the ACTUAL source module from
ab4f61feaca096ae3dae66e39d29f6e36bdca0ec, not a shadow oracle definition.

This is a deterministic, conflict-detecting request helper. It is NOT a
claim that programming a fresh answer preserves a random-oracle distribution.
Do not append its full internal log to the public observer view.
-/
set_option autoImplicit false
namespace AspisV8Privacy.FSProgrammingDraft
open AspisV8Completion.FSOracleExecution
variable {I O : Type} [DecidableEq I] [DecidableEq O]

def chosenRequest (s : State I O) (input : I) (wanted : O) : Option (O × State I O) :=
  match s.cache input with
  | none => some (query (fun _ => wanted) s input)
  | some old => if old = wanted then some (query (fun _ => wanted) s input) else none

theorem existing_conflict_aborts (s : State I O) (input : I) (old wanted : O)
    (hit : s.cache input = some old) (different : old ≠ wanted) :
    chosenRequest s input wanted = none := by
  simp [chosenRequest, hit, different]

theorem chosen_fresh_answer (s : State I O) (input : I) (wanted : O)
    (fresh : s.cache input = none) :
    (query (fun _ => wanted) s input).1 = wanted := by
  simp [query, fresh]

theorem old_entries_survive (s : State I O) (input oldInput : I) (wanted oldAnswer : O)
    (hit : s.cache oldInput = some oldAnswer) :
    (query (fun _ => wanted) s input).2.cache oldInput = some oldAnswer := by
  exact old_answer_preserved (fun _ => wanted) s input oldInput oldAnswer hit

/-- PENDING target: produce this relation from the actual prover interpreter.
A proof of this goal has not been supplied. The source prover interpreter
itself must be constructed; `literal` must not be defined to equal `model`. -/
def SourceExecutionAgreementGoal {Coins View : Type}
    (literal model : Coins → View) : Prop := ∀ coins, literal coins = model coins

#print axioms existing_conflict_aborts
#print axioms chosen_fresh_answer
#print axioms old_entries_survive
end AspisV8Privacy.FSProgrammingDraft

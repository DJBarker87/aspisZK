import Init
namespace R1Z.PV_FXM_DropCounterexample
set_option autoImplicit false

/-- The contradiction is independent of the choice of Result representation.
In particular it applies to the original op4 : {T : Type} → T → Result Unit.
The callback input does not contain the external destructor flag. -/
theorem no_world_free_callback {Input R : Type} (input : Input)
    (returned panicked : R) (distinct : returned ≠ panicked)
    (callback : Input → R) :
    ¬ (∀ flag : Bool, callback input = if flag then panicked else returned) := by
  intro h
  have a : callback input = returned := h false
  have b : callback input = panicked := h true
  exact distinct (a.symm.trans b)

inductive Outcome where
  | returned
  | panicked
  | diverged

/-- Finite witness classification, not an extracted native body. The native
world-dependent destructor is checked separately on the pinned toolchain. -/
def observed (flag : Bool) : Outcome :=
  if flag then .panicked else .returned

theorem result_distinct : Outcome.returned ≠ Outcome.panicked := by
  intro h
  cases h

theorem witness : observed false = .returned ∧ observed true = .panicked :=
  ⟨rfl, rfl⟩

/-- A one-value inhabited input carrier already refutes a uniform full-Result
projection over every external frame. Adding allocation/memory observations
cannot repair this Result mismatch. -/
theorem no_uniform_projection (callback : Unit → Outcome) :
    ¬ (∀ flag : Bool, callback () = observed flag) :=
  no_world_free_callback () .returned .panicked result_distinct callback

/-- This does not reject a state-indexed interpreter. It shows precisely the
necessary interface change: provide the world before executing the callback. -/
theorem state_indexed_nonvacuous :
    ∃ callback : Unit → Bool → Outcome,
      ∀ flag : Bool, callback () flag = observed flag :=
  ⟨fun _ flag => observed flag, fun _ => rfl⟩

#print axioms no_world_free_callback
#print axioms result_distinct
#print axioms witness
#print axioms no_uniform_projection
#print axioms state_indexed_nonvacuous
end R1Z.PV_FXM_DropCounterexample

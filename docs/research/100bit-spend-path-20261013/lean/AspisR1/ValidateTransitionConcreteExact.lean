import AspisR1.ValidateTransitionConcreteSource
import AspisR1.ResultUnitContinuation
import AspisR1TerminalValidateTransitionCandidate.EntryAppendShape

/-! Concrete capacity/Option implementation instantiated in the proved validator
entry, retaining the same source order and both failure layers. -/
set_option autoImplicit false
namespace AspisR1.ValidateTransitionConcreteExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ResultUnitContinuation
abbrev Public := AspisR1TerminalValidateTransitionCandidate.EntryPublic
abbrev Error := AspisR1TerminalValidateTransitionCandidate.EntryError
abbrev capacity := AspisR1.ValidateTransitionConcreteSource.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
abbrev optionEq := AspisR1.ValidateTransitionConcreteSource.core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64
abbrev source := AspisR1.ValidateTransitionConcreteSource.pool_v1.pair_forest_semantic_terminal.validate_transition

theorem entry_as_guard_continuation (public1 : Public)
    (cap : Result U64) (eqInst : core.cmp.PartialEq (Option U64) (Option U64)) :
    AspisR1TerminalValidateTransitionCandidate.validate_transition_entry public1 cap eqInst =
      andThenUnit
        (AspisR1TerminalValidateTransitionCandidate.validate_transition_checks public1 cap eqInst)
        (do let carry ← AspisBoundedControl.bounded_carry
              public1.transition.live_snapshot.next_pair_index
            AspisR1TerminalValidateTransitionCandidate.validate_transition_loop public1
              { start := 0#usize, «end» := 20#usize } carry) := by
  unfold AspisR1TerminalValidateTransitionCandidate.validate_transition_entry
    AspisR1TerminalValidateTransitionCandidate.validate_transition_before_loop
  unfold andThenUnit
  cases hchecks : AspisR1TerminalValidateTransitionCandidate.validate_transition_checks
      public1 cap eqInst with
  | fail err => rfl
  | div => rfl
  | ok checks =>
    cases checks with
    | Err err => rfl
    | Ok unit =>
      cases unit
      cases hcarry : AspisBoundedControl.bounded_carry
        public1.transition.live_snapshot.next_pair_index <;> rfl

theorem source_eq_entry (public1 : Public) :
    source public1 =
      AspisR1TerminalValidateTransitionCandidate.validate_transition_entry public1 capacity optionEq := by
  rw [entry_as_guard_continuation]
  unfold source AspisR1.ValidateTransitionConcreteSource.pool_v1.pair_forest_semantic_terminal.validate_transition
    AspisR1TerminalValidateTransitionCandidate.validate_transition_checks
  simp only [andThenUnit_bind,andThenUnit_if,andThenUnit_err,andThenUnit_ok]

theorem successful_concrete_noncarry_shape (public1 : Public)
    (hsuccess : source public1 = .ok (.Ok ())) :
    AspisR1.AppendSemantics.NonCarryShape
      (AspisR1.SemanticPublicModel.exactPublic public1) := by
  have hentry : AspisR1TerminalValidateTransitionCandidate.validate_transition_entry
      public1 capacity optionEq = .ok (.Ok ()) := by
    rw [← source_eq_entry]
    exact hsuccess
  exact AspisR1TerminalValidateTransitionCandidate.EntryAppendShape.successful_entry_append_shape
    public1 capacity optionEq hentry

#print axioms entry_as_guard_continuation
#print axioms source_eq_entry
#print axioms successful_concrete_noncarry_shape
end AspisR1.ValidateTransitionConcreteExact

import PV_B3P_PublicInput543227
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev TransitionOutcome543 := core.result.Result Unit reference_terminal.PoolV1PairForestSemanticTerminalErrorV1

def outcome_tag543 (r : TransitionOutcome543) : core.result.Result Unit U8 :=
  match r with | .Ok u => .Ok u | .Err e => .Err (error_tag543 e)

def outcome_untag543 (r : core.result.Result Unit U8) : TransitionOutcome543 :=
  match r with
  | .Ok u => .Ok u
  | .Err tag => .Err (if tag = 0#u8 then .InvalidPublicAmount else .InvalidAppendTransition)

theorem outcome_roundtrip543 (r : TransitionOutcome543) :
    outcome_untag543 (outcome_tag543 r) = r := by
  cases r with
  | Ok u => rfl
  | Err e => cases e <;> rfl

/-- map_err in the native adapter changes only the two error tags. Failures
of the source interpretation remain failures; this does not erase panic. -/
def observe_transition543 (r : Result TransitionOutcome543) : Result (core.result.Result Unit U8) := do
  let outcome ← r
  .ok (outcome_tag543 outcome)

def restore_transition543 (r : Result (core.result.Result Unit U8)) : Result TransitionOutcome543 := do
  let outcome ← r
  .ok (outcome_untag543 outcome)

theorem observation_roundtrip543 (r : Result TransitionOutcome543) :
    restore_transition543 (observe_transition543 r) = r := by
  cases r <;> first | rfl | exact congrArg Result.ok (outcome_roundtrip543 _)

theorem observation_injective543 : Function.Injective observe_transition543 := by
  intro a b h
  have restored := congrArg restore_transition543 h
  exact (observation_roundtrip543 a).symm.trans (restored.trans (observation_roundtrip543 b))

/-- Universal wrapper equality entails equality on every SemanticPublic.
The premise is supplied externally by a released Kani gate, never an axiom. -/
theorem transition_adapter_transfer543
    (deployed reference : reference_terminal.SemanticPublic → Result TransitionOutcome543)
    (gate : ∀ input : PublicInput543,
      observe_transition543 (deployed (public_from_input543 input)) =
      observe_transition543 (reference (public_from_input543 input))) :
    deployed = reference := by
  funext public
  have observed := gate (input_from_public543 public)
  rw [public_input_roundtrip543] at observed
  exact observation_injective543 observed

#print axioms outcome_roundtrip543
#print axioms observation_roundtrip543
#print axioms observation_injective543
#print axioms transition_adapter_transfer543
end PV_B3P_Association543227

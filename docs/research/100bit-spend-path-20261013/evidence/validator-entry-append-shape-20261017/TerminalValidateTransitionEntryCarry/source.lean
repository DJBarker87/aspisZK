import TerminalValidateTransitionLoopSource
import BoundedControlSource

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1TerminalValidateTransitionCandidate
open AspisR1SelectedMaskProbe

abbrev EntryPublic := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev EntryError := AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev EntryInvalid := AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition

/-- Exact ordered non-carry checks from the patched production
`validate_transition` block (Rust SHA 4e2099…, lines 194–206). The fixed
capacity and Option comparison implementation remain explicit source-cut
dependencies. -/
def validate_transition_checks (public1 : EntryPublic) (capacity : Result Std.U64)
    (optionEqInst : core.cmp.PartialEq (Option Std.U64) (Option Std.U64)) :
    Result (core.result.Result Unit EntryError) := do
  let b ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    public1.transition.live_snapshot.pool public1.pool
  if b then
    ok (.Err EntryInvalid)
  else
    let b1 ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      public1.transition.live_snapshot.deployment_domain public1.deployment_domain
    if b1 then
      ok (.Err EntryInvalid)
    else
      if public1.transition.live_snapshot.sequence !=
        public1.transition.live_snapshot.next_pair_index then
        ok (.Err EntryInvalid)
      else
        let i ← capacity
        if public1.transition.live_snapshot.next_pair_index >= i then
          ok (.Err EntryInvalid)
        else
          let o ← lift (U64.checked_add
            public1.transition.live_snapshot.next_pair_index 1#u64)
          let b2 ← core.cmp.PartialEq.ne.trait_default optionEqInst o
            (some public1.transition.candidate_afterstate.next_pair_index)
          if b2 then ok (.Err EntryInvalid) else ok (.Ok ())

/-- The exact patched source suffix after the prechecks: compute the bounded
carry, then call the retained exact loop with range `[0,20)`. -/
def validate_transition_before_loop (public1 : EntryPublic) (capacity : Result Std.U64)
    (optionEqInst : core.cmp.PartialEq (Option Std.U64) (Option Std.U64)) :
    Result (core.result.Result Std.Usize EntryError) := do
  let checks ← validate_transition_checks public1 capacity optionEqInst
  match checks with
  | .Err e => ok (.Err e)
  | .Ok () =>
    let carry ← AspisBoundedControl.bounded_carry
      public1.transition.live_snapshot.next_pair_index
    ok (.Ok carry)

def validate_transition_entry (public1 : EntryPublic) (capacity : Result Std.U64)
    (optionEqInst : core.cmp.PartialEq (Option Std.U64) (Option Std.U64)) :
    Result (core.result.Result Unit EntryError) := do
  let carryResult ← validate_transition_before_loop public1 capacity optionEqInst
  match carryResult with
  | .Err e => ok (.Err e)
  | .Ok carry =>
    validate_transition_loop public1 { start := 0#usize, «end» := 20#usize } carry

private theorem bind_ok {α β : Type} {x : Result α} {f : α → Result β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- Successful patched entry source implies the exact bounded carry call and
the same successful `[0,20)` loop call. No independent carry or loop-result
premise is assumed. -/
theorem entry_success_reaches_bounded_carry_and_loop (public1 : EntryPublic)
    (capacity : Result Std.U64)
    (optionEqInst : core.cmp.PartialEq (Option Std.U64) (Option Std.U64))
    (hsuccess : validate_transition_entry public1 capacity optionEqInst = .ok (.Ok ())) :
    ∃ carry,
      AspisBoundedControl.bounded_carry public1.transition.live_snapshot.next_pair_index =
        .ok carry ∧
      validate_transition_loop public1 { start := 0#usize, «end» := 20#usize } carry =
        .ok (.Ok ()) := by
  unfold validate_transition_entry at hsuccess
  rcases bind_ok hsuccess with ⟨carryResult, hprefix, hcontinue⟩
  cases carryResult with
  | Err e => simp at hcontinue
  | Ok carry =>
    have hbefore : validate_transition_before_loop public1 capacity optionEqInst =
        .ok (.Ok carry) := hprefix
    unfold validate_transition_before_loop at hbefore
    rcases bind_ok hbefore with ⟨checks, hchecks, hafter⟩
    cases checks with
    | Err e => simp at hafter
    | Ok unit =>
      cases unit
      rcases bind_ok hafter with ⟨carryActual, hcarry, hresult⟩
      have hsame : carryActual = carry := by
        have hinner : core.result.Result.Ok carryActual = core.result.Result.Ok carry :=
          Result.ok.inj hresult
        exact core.result.Result.Ok.inj hinner
      refine ⟨carry, ?_, hcontinue⟩
      simpa [hsame] using hcarry

#print axioms entry_success_reaches_bounded_carry_and_loop
end AspisR1TerminalValidateTransitionCandidate

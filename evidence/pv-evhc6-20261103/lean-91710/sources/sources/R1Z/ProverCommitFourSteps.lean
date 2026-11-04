import R1Z.ProverCommitStepLoop

/-! Symbolic sequential scalar calls, retaining each final failure state.
The extracted tower caller is exactly four calls in left-to-right order. -/
set_option autoImplicit false
namespace R1Z.ProverCommitFourSteps
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash Sample transition)
abbrev Error := state_only_hiding.StateOnlyMaskBuildError

def collect {S : Type} (step : S → Result (Sample × S)) :
    Nat → S → Result (core.result.Result (List U32) Error × S)
  | 0, s => ok (.Ok [], s)
  | n+1, s => do
    let (sample, after) ← step s
    match sample with
    | .Err e => ok (.Err e, after)
    | .Ok a =>
      let (tail, final) ← collect step n after
      match tail with
      | .Err e => ok (.Err e, final)
      | .Ok values => ok (.Ok (a::values), final)

theorem collect_congr {S : Type} (left right : S → Result (Sample × S))
    (same : ∀ s, left s = right s) (n : Nat) (s : S) :
    collect left n s = collect right n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [collect, same]
    cases h : right s with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      cases sample with
      | Err e => rfl
      | Ok a => simp only [bind_tc_ok, ih]

theorem collect_extracted_steps (hash : Hash) (domain : Slice U8)
    (n : Nat) (state : State) :
    collect (prover_commit_reference.limb_caller hash domain) n state =
    collect (fun s => R1Z.ProverCommitExtractedStep.iterate
      (transition hash domain) 16 (.Err .MaskSampleExhausted, s)) n state := by
  apply collect_congr
  exact R1Z.ProverCommitStepLoop.caller_step_induction hash domain

def coordinates (q : aspis_core.field.QM31) : List U32 :=
  [q.c0.a, q.c0.b, q.c1.a, q.c1.b]

theorem qm31_collect (hash : Hash) (domain : Slice U8) (state : State) :
    (do
      let (sample, after) ← prover_commit_reference.qm31_caller hash domain state
      match sample with
      | .Err e => ok (.Err e, after)
      | .Ok q => ok (.Ok (coordinates q), after)) =
    collect (prover_commit_reference.limb_caller hash domain) 4 state := by
  simp only [prover_commit_reference.qm31_caller, collect, bind_assoc_eq]
  cases h1 : prover_commit_reference.limb_caller hash domain state with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨sample, state1⟩
    simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    cases sample with
    | Err e => rfl
    | Ok a1 =>
      cases h2 : prover_commit_reference.limb_caller hash domain state1 with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        rcases pair with ⟨sample, state2⟩
        simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
        cases sample with
        | Err e => rfl
        | Ok a2 =>
          cases h3 : prover_commit_reference.limb_caller hash domain state2 with
          | fail e => rfl
          | div => rfl
          | ok pair =>
            rcases pair with ⟨sample, state3⟩
            simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
            cases sample with
            | Err e => rfl
            | Ok a3 =>
              cases h4 : prover_commit_reference.limb_caller hash domain state3 with
              | fail e => rfl
              | div => rfl
              | ok pair =>
                rcases pair with ⟨sample, state4⟩
                simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
                cases sample with
                | Err e => rfl
                | Ok a4 =>
                  rfl

#print axioms collect_congr
#print axioms collect_extracted_steps
#print axioms qm31_collect
end R1Z.ProverCommitFourSteps

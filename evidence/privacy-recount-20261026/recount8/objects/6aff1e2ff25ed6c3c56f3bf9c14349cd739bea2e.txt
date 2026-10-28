import R1Z.ProverCommitOwnedCursorProgress
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State scalarFinite)
open R1Z.ProverCommitFourSteps (collect)

theorem scalarFinite_progress {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (n : Nat)
    (state after : State) (value : U32) (before : valid blocks state)
    (success : scalarFinite (blockHash answers) domain n state = ok (.Ok value, after)) :
    valid blocks after ∧ position state < position after := by
  induction n generalizing state after value with
  | zero => cases success
  | succ n ih =>
    rw [R1Z.ProverCommitStepLoop.scalarFinite_succ] at success
    obtain ⟨pair, next, rest⟩ := bind_success _ _ _ success
    rcases pair with ⟨word, current⟩
    simp only [Aeneas.Std.uncurry_apply_pair] at rest
    have progress := next_progress answers domain state current word capacity before next
    split at rest
    · cases rest
      exact ⟨progress.1, by omega⟩
    · have later := ih current after value progress.1 rest
      exact ⟨later.1, by omega⟩

theorem scalar_progress {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64)
    (state after : State) (value : U32) (before : valid blocks state)
    (success : prover_commit_reference.limb_caller (blockHash answers) domain state = ok (.Ok value, after)) :
    valid blocks after ∧ position state < position after := by
  rw [R1Z.ProverCommitStepLoop.caller_sixteen] at success
  exact scalarFinite_progress answers domain capacity 16 state after value before success

theorem collect_progress {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (n : Nat)
    (state after : State) (values : List U32) (before : valid blocks state)
    (success : collect (prover_commit_reference.limb_caller (blockHash answers) domain)
      n state = ok (.Ok values, after)) :
    valid blocks after ∧ position state + n ≤ position after := by
  induction n generalizing state after values with
  | zero =>
    cases success
    exact ⟨before, by omega⟩
  | succ n ih =>
    simp only [collect] at success
    obtain ⟨pair, sampled, rest⟩ := bind_success _ _ _ success
    rcases pair with ⟨sample, current⟩
    simp only [Aeneas.Std.uncurry_apply_pair] at rest
    cases sample with
    | Err e => cases rest
    | Ok value =>
      have first := scalar_progress answers domain capacity state current value before sampled
      obtain ⟨pair, collected, rest⟩ := bind_success _ _ _ rest
      rcases pair with ⟨tail, final⟩
      simp only [Aeneas.Std.uncurry_apply_pair] at rest
      cases tail with
      | Err e => cases rest
      | Ok tail =>
        cases rest
        have later := ih current after tail first.1 collected
        exact ⟨later.1, by omega⟩

/-- A universal bound on successfully produced raw samples from a finite
backend. In particular the nine-block local Kani ROM is not a whole-array ROM. -/
theorem samples_bound {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (n : Nat)
    (values : List U32) (success : samples (blockHash answers) domain n = some values) :
    n ≤ 8*blocks := by
  unfold samples at success
  cases h : collect (prover_commit_reference.limb_caller (blockHash answers) domain) n initial with
  | fail e => simp only [h, reduceCtorEq] at success
  | div => simp only [h, reduceCtorEq] at success
  | ok pair =>
    rcases pair with ⟨sample, after⟩
    cases sample with
    | Err e => simp only [h, reduceCtorEq] at success
    | Ok vs =>
      have start : valid blocks initial := by simp [valid, initial]
      have progress := collect_progress answers domain capacity n initial after vs start h
      have bound := position_bound progress.1
      have zero : position initial = 0 := by rfl
      rw [zero] at progress
      omega

#print axioms scalarFinite_progress
#print axioms scalar_progress
#print axioms collect_progress
#print axioms samples_bound
end R1Z.ProverCommitOwnedDecoder

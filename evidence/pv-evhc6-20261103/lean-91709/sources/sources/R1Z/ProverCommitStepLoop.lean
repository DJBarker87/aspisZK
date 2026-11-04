import AspisR1ProverStep8.Funs
import R1Z.ProverCommitExtractedStep

set_option autoImplicit false
namespace R1Z.ProverCommitStepLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1ProverStep8
abbrev State := prover_commit_reference.State
abbrev Hash := Slice (Slice U8) → Result (Aeneas.Std.Array U8 32#usize)
open R1Z.ProverCommitExtractedStep (iterate)

theorem iterator_more (attempts : I32) (running : attempts.val < 16) :
    ∃ after : core.ops.range.Range I32,
      core.iter.range.IteratorRange.next core.iter.range.StepI32
        {start := attempts, «end» := 16#i32} = ok (some attempts, after) ∧
      after.start.val = attempts.val + 1 ∧ after.end = 16#i32 := by
  have hmax : attempts.val + 1 ≤ I32.max := by scalar_tac
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.PartialOrdI32,
    core.cmp.impls.PartialOrdI32.lt, core.clone.CloneI32,
    core.clone.impls.CloneI32.clone, liftFun1, liftFun2, bind_tc_ok]
  simp [running, core.iter.range.IScalarStep.forward_checked, hmax]

theorem iterator_done (attempts : I32) (stopped : 16 ≤ attempts.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32
      {start := attempts, «end» := 16#i32} =
      ok (none, {start := attempts, «end» := 16#i32}) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.PartialOrdI32,
    core.cmp.impls.PartialOrdI32.lt, not_lt.mpr stopped]

abbrev Sample := core.result.Result aspis_core.field.M31
  state_only_hiding.StateOnlyMaskBuildError

def finite (hash : Hash) (domain : Slice U8) : Nat → State →
    Result (State × Option (Sample × State))
  | 0, state => ok (state, none)
  | n+1, state => do
    let (word, after) ← prover_commit_reference.next hash domain state
    let candidate ← lift (word &&& 2147483647#u32)
    if candidate < aspis_core.field.P then
      ok (after, some (.Ok candidate, after))
    else finite hash domain n after

theorem loop_finite (hash : Hash) (domain : Slice U8) (n : Nat)
    (state : State) (attempts : I32)
    (remaining : attempts.val + (n : Int) = 16) :
    prover_commit_reference.limb_caller_loop
      {start := attempts, «end» := 16#i32} hash domain state =
      finite hash domain n state := by
  induction n generalizing state attempts with
  | zero =>
    have stopped : 16 ≤ attempts.val := by omega
    rw [prover_commit_reference.limb_caller_loop, loop]
    simp only [prover_commit_reference.limb_caller_loop.body,
      iterator_done attempts stopped, bind_tc_ok, Aeneas.Std.uncurry_apply_pair,
      finite]
  | succ n ih =>
    have running : attempts.val < 16 := by omega
    obtain ⟨after, heq, hstart, hend⟩ := iterator_more attempts running
    rw [prover_commit_reference.limb_caller_loop, loop]
    simp only [prover_commit_reference.limb_caller_loop.body, heq,
      bind_tc_ok, Aeneas.Std.uncurry_apply_pair, finite]
    cases hn : prover_commit_reference.next hash domain state with
    | fail error => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨word, state'⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair, lift]
      split_ifs
      · rfl
      · have hafter : after = {start := after.start, «end» := 16#i32} := by
          cases after
          simp_all
        rw [hafter]
        exact ih state' _ (by omega)

theorem caller_sixteen (hash : Hash) (domain : Slice U8) (state : State) :
    prover_commit_reference.limb_caller hash domain state = (do
      let (after, pending) ← finite hash domain 16 state
      match pending with
      | none => ok (.Err .MaskSampleExhausted, after)
      | some pair => ok pair) := by
  unfold prover_commit_reference.limb_caller
  rw [loop_finite hash domain 16 state 0#i32 (by decide)]
  rfl

theorem try_success (hash : Hash) (domain : Slice U8) (state : State)
    (value : U32) :
    prover_commit_reference.try_step hash domain state (.Ok value) =
      ok (.Ok value, state) := rfl

def transition (hash : Hash) (domain : Slice U8) (s : Sample × State) :=
  prover_commit_reference.try_step hash domain s.2 s.1

theorem iterate_success (hash : Hash) (domain : Slice U8) (n : Nat)
    (state : State) (value : U32) :
    iterate (transition hash domain) n (.Ok value, state) = ok (.Ok value, state) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate, transition, try_success, bind_tc_ok] using ih

def scalarFinite (hash : Hash) (domain : Slice U8) (n : Nat) (state : State) :
    Result (Sample × State) := do
  let (after, pending) ← finite hash domain n state
  match pending with
  | none => ok (.Err .MaskSampleExhausted, after)
  | some pair => ok pair

theorem scalarFinite_succ (hash : Hash) (domain : Slice U8) (n : Nat) (state : State) :
    scalarFinite hash domain (n+1) state = (do
      let (word, after) ← prover_commit_reference.next hash domain state
      if word &&& 2147483647#u32 < aspis_core.field.P then
        ok (.Ok (word &&& 2147483647#u32), after)
      else scalarFinite hash domain n after) := by
  simp only [scalarFinite, finite, bind_assoc_eq]
  cases h : prover_commit_reference.next hash domain state with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨word, after⟩
    simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair, lift]
    split_ifs <;> rfl

theorem scalar_induction (hash : Hash) (domain : Slice U8) (n : Nat) (state : State) :
    scalarFinite hash domain n state =
      iterate (transition hash domain) n (.Err .MaskSampleExhausted, state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [scalarFinite_succ]
    simp only [iterate, transition, prover_commit_reference.try_step, lift]
    cases h : prover_commit_reference.next hash domain state with
    | fail error => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨word, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      split_ifs
      · exact (iterate_success hash domain n after _).symm
      · exact ih after

theorem caller_step_induction (hash : Hash) (domain : Slice U8) (state : State) :
    prover_commit_reference.limb_caller hash domain state =
      iterate (transition hash domain) 16 (.Err .MaskSampleExhausted, state) := by
  rw [caller_sixteen]
  exact scalar_induction hash domain 16 state

#print axioms try_success
#print axioms iterate_success
#print axioms scalarFinite_succ
#print axioms scalar_induction
#print axioms caller_step_induction
#print axioms iterator_more
#print axioms iterator_done
#print axioms loop_finite
#print axioms caller_sixteen
end R1Z.ProverCommitStepLoop

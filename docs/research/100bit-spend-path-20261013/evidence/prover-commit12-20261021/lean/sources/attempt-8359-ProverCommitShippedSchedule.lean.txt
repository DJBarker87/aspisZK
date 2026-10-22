import R1Z.ProverCommitCallerLoop
/-! Fixed scalar schedules after abstraction of the verified next-word call.
Generated from AspisR1ProverStreams; see the literal source receipts.
No claim that this abstraction alone identifies the whole shipped caller. -/
set_option autoImplicit false
namespace R1Z.ProverCommitShippedSchedule
open Aeneas Aeneas.Std Result ControlFlow AspisR1ProverCaller7
variable {State : Type} (nextWord : State → Result (U32 × State))
abbrev Sample := core.result.Result aspis_core.field.M31
  state_only_hiding.StateOnlyMaskBuildError
theorem usize_more (attempts : Usize) (running : attempts.val < 16) :
    ∃ after : core.ops.range.Range Usize,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
        {start := attempts, «end» := 16#usize} = ok (some attempts, after) ∧
      after.start.val = attempts.val + 1 ∧ after.end = 16#usize := by
  have hmax : attempts.val + 1 ≤ Usize.max := by scalar_tac
  have hlt : attempts.val < UScalar.max .Usize := by scalar_tac
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt, core.clone.CloneUsize,
    core.clone.impls.CloneUsize.clone, liftFun1, liftFun2, bind_tc_ok]
  simp [running, core.iter.range.UScalarStep.forward_checked, hlt]

theorem usize_done (attempts : Usize) (stopped : 16 ≤ attempts.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
      {start := attempts, «end» := 16#usize} =
      ok (none, {start := attempts, «end» := 16#usize}) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt, not_lt.mpr stopped]

namespace mask
def body (nextWord : State → Result (U32 × State))
  (iter : core.ops.range.Range Std.Usize)
  (self : State) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    State) (State × (Option
    (core.result.Result aspis_core.field.M31
    state_only_hiding.StateOnlyMaskBuildError))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (self, none))
  | some _ =>
    let (i, self1) ← nextWord self
    let candidate ← lift (i &&& 2147483647#u32)
    let i1 := aspis_core.field.P
    if candidate < i1
    then ok (done (self1, some (core.result.Result.Ok candidate)))
    else ok (cont (iter1, self1))



def run (nextWord : State → Result (U32 × State))
  (iter : core.ops.range.Range Std.Usize)
  (self : State) :
  Result (State × (Option (core.result.Result
    aspis_core.field.M31 state_only_hiding.StateOnlyMaskBuildError)))
  := do
  loop
    (fun (iter1, self1) => body nextWord iter1
      self1)
    (iter, self)


def scalar (nextWord : State → Result (U32 × State))
  (self : State) :
  Result ((core.result.Result aspis_core.field.M31
    state_only_hiding.StateOnlyMaskBuildError) ×
    State)
  := do
  let (self1, pending_return) ←
    run nextWord
      { start := 0#usize, «end» := 16#usize
      } self
  match pending_return with
  | none =>
    ok (core.result.Result.Err
      state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted, self1)
  | some r => ok (r, self1)

def finite (nextWord : State → Result (U32 × State)) : Nat → State → Result (State × Option Sample)
  | 0, state => ok (state, none)
  | n+1, state => do
    let (word, after) ← nextWord state
    let candidate ← lift (word &&& 2147483647#u32)
    let p := aspis_core.field.P
    if candidate < p then ok (after, some (.Ok candidate))
    else finite nextWord n after

theorem loop_finite (n : Nat) (state : State) (attempts : Usize)
    (remaining : attempts.val + (n) = 16) :
    run nextWord
      {start := attempts, «end» := 16#usize} state = finite nextWord n state := by
  induction n generalizing state attempts with
  | zero =>
    have stopped : 16 ≤ attempts.val := by omega
    rw [run, loop]
    simp only [body,
      usize_done attempts stopped, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, finite]
  | succ n ih =>
    have running : attempts.val < 16 := by omega
    obtain ⟨after, heq, hstart, hend⟩ := usize_more attempts running
    rw [run, loop]
    simp only [body, heq,
      bind_tc_ok, Aeneas.Std.uncurry_apply_pair, finite]
    cases hn : nextWord state with
    | fail error => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨word, state'⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair, lift]
      split_ifs
      · rfl
      · have hafter : after = {start := after.start, «end» := 16#usize} := by
          cases after
          simp_all
        rw [hafter]
        exact ih state' _ (by omega)

theorem scalar_sixteen (state : State) :
    scalar nextWord state = (do
      let (after, pending) ← finite nextWord 16 state
      match pending with
      | none => ok (.Err .MaskSampleExhausted, after)
      | some sample => ok (sample, after)) := by
  unfold scalar
  rw [loop_finite nextWord 16 state 0#usize (by decide)]
  rfl

#print axioms loop_finite
#print axioms scalar_sixteen
end mask

namespace source
def body (nextWord : State → Result (U32 × State))
  (iter : core.ops.range.Range Std.I32)
  (self : State) :
  Result (ControlFlow ((core.ops.range.Range Std.I32) ×
    State)
    (State × (Option (core.result.Result
    aspis_core.field.M31 state_only_hiding.StateOnlyMaskBuildError))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepI32 iter
  match o with
  | none => ok (done (self, none))
  | some _ =>
    let (i, self1) ←
      nextWord self
    let candidate ← lift (i &&& 2147483647#u32)
    let i1 := aspis_core.field.P
    if candidate < i1
    then ok (done (self1, some (core.result.Result.Ok candidate)))
    else ok (cont (iter1, self1))



def run (nextWord : State → Result (U32 × State))
  (iter : core.ops.range.Range Std.I32)
  (self : State) :
  Result (State × (Option
    (core.result.Result aspis_core.field.M31
    state_only_hiding.StateOnlyMaskBuildError)))
  := do
  loop
    (fun (iter1, self1) =>
      body nextWord iter1 self1)
    (iter, self)


def scalar (nextWord : State → Result (U32 × State))
  (self : State) :
  Result ((core.result.Result aspis_core.field.M31
    state_only_hiding.StateOnlyMaskBuildError) ×
    State)
  := do
  let (self1, pending_return) ←
    run nextWord
      { start := 0#i32, «end» := 16#i32 } self
  match pending_return with
  | none =>
    ok (core.result.Result.Err
      state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted, self1)
  | some r => ok (r, self1)

def finite (nextWord : State → Result (U32 × State)) : Nat → State → Result (State × Option Sample)
  | 0, state => ok (state, none)
  | n+1, state => do
    let (word, after) ← nextWord state
    let candidate ← lift (word &&& 2147483647#u32)
    let p := aspis_core.field.P
    if candidate < p then ok (after, some (.Ok candidate))
    else finite nextWord n after

theorem loop_finite (n : Nat) (state : State) (attempts : I32)
    (remaining : attempts.val + ((n : Int)) = 16) :
    run nextWord
      {start := attempts, «end» := 16#i32} state = finite nextWord n state := by
  induction n generalizing state attempts with
  | zero =>
    have stopped : 16 ≤ attempts.val := by omega
    rw [run, loop]
    simp only [body,
      ProverCommitCallerLoop.iterator_done attempts stopped, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, finite]
  | succ n ih =>
    have running : attempts.val < 16 := by omega
    obtain ⟨after, heq, hstart, hend⟩ := ProverCommitCallerLoop.iterator_more attempts running
    rw [run, loop]
    simp only [body, heq,
      bind_tc_ok, Aeneas.Std.uncurry_apply_pair, finite]
    cases hn : nextWord state with
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

theorem scalar_sixteen (state : State) :
    scalar nextWord state = (do
      let (after, pending) ← finite nextWord 16 state
      match pending with
      | none => ok (.Err .MaskSampleExhausted, after)
      | some sample => ok (sample, after)) := by
  unfold scalar
  rw [loop_finite nextWord 16 state 0#i32 (by decide)]
  rfl

#print axioms loop_finite
#print axioms scalar_sixteen
end source

#print axioms usize_more
#print axioms usize_done
end R1Z.ProverCommitShippedSchedule

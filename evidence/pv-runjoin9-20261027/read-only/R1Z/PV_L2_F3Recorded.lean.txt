import R1Z.ProverCommitOwnedDecoder

/-! Failure-preserving recording on the ACTUAL extracted owned scalar caller.
This records reference calls/cursors and their answers, including refill
requests. It is not a native cost certificate or a hiding law for raw answers.
Raw answers here are retained proof inputs, not all declared public leakage. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F3Recorded
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash Sample scalarFinite)
open R1Z.ProverCommitStreamSource (blockSlices)

structure Read where
  before : State
  answer : Result (U32 × State)

def scalar (hash : Hash) (domain : Slice U8) : Nat → State →
    Result (Sample × State) × List Read
  | 0, state => (ok (.Err .MaskSampleExhausted,state),[])
  | n+1, state =>
    let next := prover_commit_reference.next hash domain state
    match next with
    | .fail e => (.fail e,[⟨state,next⟩])
    | .div => (.div,[⟨state,next⟩])
    | .ok (word,after) =>
      if word &&& 2147483647#u32 < aspis_core.field.P then
        (ok (.Ok (word &&& 2147483647#u32),after),[⟨state,next⟩])
      else let rest := scalar hash domain n after
           (rest.1,⟨state,next⟩::rest.2)

theorem scalar_erases (hash : Hash) (domain : Slice U8) (n : Nat) (state : State) :
    (scalar hash domain n state).1 = scalarFinite hash domain n state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [R1Z.ProverCommitStepLoop.scalarFinite_succ]
    unfold scalar
    cases hn : prover_commit_reference.next hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨word,after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      split_ifs
      · rfl
      · exact ih after

theorem source_scalar_erases (hash : Hash) (domain : Slice U8) (state : State) :
    (scalar hash domain 16 state).1 = prover_commit_reference.limb_caller hash domain state := by
  rw [scalar_erases, R1Z.ProverCommitStepLoop.caller_sixteen]
  rfl

/-- The refill request's domain, seed, counter frame is the actual frame
of the extracted reference; all of its successful and failing answers stay. -/
def refill (domain : Slice U8) (read : Read) : Option (Slice (Slice U8)) :=
  if read.before.word = 8#usize then
    some (blockSlices domain read.before.seed read.before.counter)
  else none

def collect (hash : Hash) (domain : Slice U8) : Nat → State →
    Result (core.result.Result (List U32) state_only_hiding.StateOnlyMaskBuildError × State) × List Read
  | 0, state => (ok (.Ok [],state),[])
  | n+1, state =>
    let sample := scalar hash domain 16 state
    match sample.1 with
    | .fail e => (.fail e,sample.2)
    | .div => (.div,sample.2)
    | .ok (.Err e,after) => (ok (.Err e,after),sample.2)
    | .ok (.Ok value,after) =>
      let rest := collect hash domain n after
      ((do let (values,final) ← rest.1
           match values with
           | .Err e => ok (.Err e,final)
           | .Ok values => ok (.Ok (value::values),final)),sample.2 ++ rest.2)

theorem collect_erases (hash : Hash) (domain : Slice U8) (n : Nat) (state : State) :
    (collect hash domain n state).1 = R1Z.ProverCommitFourSteps.collect
      (prover_commit_reference.limb_caller hash domain) n state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    unfold collect R1Z.ProverCommitFourSteps.collect
    rw [← source_scalar_erases]
    cases hn : (scalar hash domain 16 state).1 with
    | fail e => simp only [hn, bind_tc_fail]
    | div => simp only [hn, bind_tc_div]
    | ok pair =>
      rcases pair with ⟨sample,after⟩
      cases sample with
      | Err e => simp only [hn, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      | Ok value =>
        simp only [hn, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
        rw [ih]
        rfl

/-- Four-limb partial failure returns at its actual prefix; the whole existing
extracted QM31 caller, not a stubbed scalar, is the erased result. -/
theorem qm31_erases (hash : Hash) (domain : Slice U8) (state : State) :
    (collect hash domain 4 state).1 = (do
      let (sample,after) ← prover_commit_reference.qm31_caller hash domain state
      match sample with
      | .Err e => ok (.Err e,after)
      | .Ok q => ok (.Ok (R1Z.ProverCommitFourSteps.coordinates q),after)) := by
  rw [collect_erases]
  exact (R1Z.ProverCommitFourSteps.qm31_collect hash domain state).symm

#print axioms scalar_erases
#print axioms source_scalar_erases
#print axioms collect_erases
#print axioms qm31_erases
end R1Z.PV_L2_F3Recorded

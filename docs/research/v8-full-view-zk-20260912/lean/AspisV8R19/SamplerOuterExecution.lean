import AspisR72Sampler.Funs
import Mathlib.Tactic

/-! Exact finite unfolding of the actual generated outer sampler. Inner
sampling and circle calls remain the actual functions, not assumed models.
This is not yet their byte/oracle-trace correspondence. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerOuterExecution
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler

abbrev Output := (core.result.Result circle.SecureCirclePoint
  transcript.CirclePointSampleError) × transcript.Transcript

def bounded : Nat → transcript.Transcript → Result Output
  | 0,s => .ok (.Err .ParameterSampleExhausted,s)
  | n+1,s => do
      let (r,s1) ← transcript.Transcript.challenge_qm31 s
      match r with
      | .Err _ => .ok (.Err .ChallengeSampleExhausted,s1)
      | .Ok t =>
          let p ← circle.secure_ood_circle_point_from_parameter t
          match p with
          | .Ok point => .ok (.Ok point,s1)
          | .Err _ => bounded n s1

theorem range_next (r : core.ops.range.Range U32) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 r =
    if h : r.start.val < r.end.val then
      .ok (some r.start, {start := (UScalar.ofNatCore (r.start.val+1)
        (by have := r.end.hBounds; omega)), «end» := r.end})
    else .ok (none, r) := by
  by_cases h : r.start.val < r.end.val
  · have hb : r.start.val + 1 ≤ UScalar.max .U32 := by
      rw [UScalar.max]
      have := r.end.hBounds
      omega
    have hb' : r.start.val < UScalar.max .U32 := by omega
    have hb32 : r.start.val < U32.max := by
      simpa only [UScalar.max,U32.max,U32.numBits] using hb'
    simp [core.iter.range.IteratorRange.next,core.iter.range.StepU32,
      core.iter.range.UScalarStep,core.cmp.PartialOrdU32,
      core.cmp.impls.PartialOrdU32.lt,core.clone.CloneU32,
      liftFun2,liftFun1,h,core.iter.range.UScalarStep.forward_checked,hb32]
  · simp [core.iter.range.IteratorRange.next,core.iter.range.StepU32,
      core.iter.range.UScalarStep,core.cmp.PartialOrdU32,
      core.cmp.impls.PartialOrdU32.lt,liftFun2,h]

theorem map_error (r : core.result.Result field.QM31 transcript.ChallengeSampleExhausted) :
    AspisR72Sampler.core.result.Result.map_err
      transcript.Transcript.challenge_secure_circle_point.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedCirclePointSampleError
      r () = .ok (match r with
        | .Ok t => .Ok t
        | .Err _ => .Err transcript.CirclePointSampleError.ChallengeSampleExhausted) := by
  cases r <;> rfl

theorem loop_execution (n : Nat) (r : core.ops.range.Range U32) (s : transcript.Transcript)
    (hn : r.end.val-r.start.val = n) :
    transcript.Transcript.challenge_secure_circle_point_loop r s = bounded n s := by
  induction n generalizing r s with
  | zero =>
      have h : ¬ r.start.val < r.end.val := by omega
      rw [transcript.Transcript.challenge_secure_circle_point_loop,loop.eq_def]
      simp only [transcript.Transcript.challenge_secure_circle_point_loop.body,
        range_next,dif_neg h,bind_tc_ok,bounded]
  | succ n ih =>
      have h : r.start.val < r.end.val := by omega
      let r' : core.ops.range.Range U32 :=
        {start := UScalar.ofNatCore (r.start.val+1)
          (by have := r.end.hBounds; omega), «end» := r.end}
      have hn' : r'.end.val-r'.start.val = n := by
        change r.end.val-(r.start.val+1)=n; omega
      rw [transcript.Transcript.challenge_secure_circle_point_loop,loop.eq_def]
      simp only [transcript.Transcript.challenge_secure_circle_point_loop.body,
        range_next,dif_pos h,bind_tc_ok,map_error,bounded]
      cases hs : transcript.Transcript.challenge_qm31 s with
      | fail e => simp
      | div => simp
      | ok pair =>
          rcases pair with ⟨result,s1⟩
          cases result with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          | Ok t =>
              simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
              cases hp : circle.secure_ood_circle_point_from_parameter t with
              | fail e => simp
              | div => simp
              | ok result =>
                  cases result with
                  | Ok p => simp
                  | Err e =>
                      simp only [bind_tc_ok]
                      simpa only [transcript.Transcript.challenge_secure_circle_point_loop,
                        transcript.Transcript.challenge_secure_circle_point_loop.body,
                        range_next,map_error,core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok,r'] using ih r' s1 hn'

theorem entry_three (s : transcript.Transcript) :
    transcript.Transcript.challenge_secure_circle_point s = bounded 3 s := by
  apply loop_execution
  simp only [transcript.CIRCLE_POINT_RETRY_LIMIT]
  rfl
theorem probe_three (s : transcript.Transcript) : sampler_probe s = bounded 3 s := entry_three s
theorem zero_no_calls (s : transcript.Transcript) :
    bounded 0 s = .ok (.Err .ParameterSampleExhausted,s) := rfl
theorem inner_error_stops (n : Nat) (s s1 : transcript.Transcript)
    (h : transcript.Transcript.challenge_qm31 s = .ok (.Err (),s1)) :
    bounded (n+1) s = .ok (.Err .ChallengeSampleExhausted,s1) := by simp [bounded,h]
theorem accepted_stops (n : Nat) (s s1 : transcript.Transcript)
    (t : field.QM31) (p : circle.SecureCirclePoint)
    (h : transcript.Transcript.challenge_qm31 s = .ok (.Ok t,s1))
    (hp : circle.secure_ood_circle_point_from_parameter t = .ok (.Ok p)) :
    bounded (n+1) s = .ok (.Ok p,s1) := by simp [bounded,h,hp]
theorem rejected_retains_state (n : Nat) (s s1 : transcript.Transcript)
    (t : field.QM31) (e : circle.CirclePointError)
    (h : transcript.Transcript.challenge_qm31 s = .ok (.Ok t,s1))
    (hp : circle.secure_ood_circle_point_from_parameter t = .ok (.Err e)) :
    bounded (n+1) s = bounded n s1 := by simp [bounded,h,hp]
theorem inner_failure_propagates (n : Nat) (s : transcript.Transcript) (e : Error)
    (h : transcript.Transcript.challenge_qm31 s = .fail e) :
    bounded (n+1) s = .fail e := by simp [bounded,h]
theorem inner_divergence_propagates (n : Nat) (s : transcript.Transcript)
    (h : transcript.Transcript.challenge_qm31 s = .div) :
    bounded (n+1) s = .div := by simp [bounded,h]

#print axioms range_next
#print axioms map_error
#print axioms loop_execution
#print axioms entry_three
#print axioms probe_three
#print axioms zero_no_calls
#print axioms inner_error_stops
#print axioms accepted_stops
#print axioms rejected_retains_state
#print axioms inner_failure_propagates
#print axioms inner_divergence_propagates
#print axioms transcript.Transcript.challenge_qm31
#print axioms transcript.Transcript.squeeze_block
#print axioms transcript.Transcript.challenge_secure_circle_point
end AspisV8R19.SamplerOuterExecution

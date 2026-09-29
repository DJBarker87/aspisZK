import AspisV8R19.SamplerObservedChallenge
import AspisV8R19.SamplerOuterExecution

/-! Exact finite execution of the instrumented outer retry loop. The source
circle map and QM31 sampler remain actual calls. No successful challenge,
freshness, independence or backend-totality hypothesis is used here. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedCircleLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler
open SamplerObservation SamplerObservedLaws
open SamplerOuterExecution (Output range_next map_error)

def bounded : Nat → transcript.Transcript → Observed Output
  | 0,s => pure (.Err .ParameterSampleExhausted,s)
  | n+1,s => do
      let (r,s1) ← SamplerObservedSource.challenge_qm31 s
      match r with
      | .Err _ => pure (.Err .ChallengeSampleExhausted,s1)
      | .Ok t =>
          let p ← circle.secure_ood_circle_point_from_parameter t
          match p with
          | .Ok point => pure (.Ok point,s1)
          | .Err _ => bounded n s1

theorem loop_execution (n : Nat) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (hn : r.end.val-r.start.val=n) (history : Trace) :
    SamplerObservedSource.challenge_secure_circle_point_loop r s history =
      bounded n s history := by
  induction n generalizing r s history with
  | zero =>
      have hr : ¬r.start.val < r.end.val := by omega
      rw [SamplerObservedSource.challenge_secure_circle_point_loop,loop_unfold]
      simp only [SamplerObservedSource.challenge_secure_circle_point_loop.body,
        range_next,dif_neg hr,bind_apply,lift_apply,pure_apply,bind_tc_ok,bounded]
  | succ n ih =>
      have hr : r.start.val < r.end.val := by omega
      let r' : core.ops.range.Range U32 :=
        {start := UScalar.ofNatCore (r.start.val+1)
          (by have := r.end.hBounds; omega), «end» := r.end}
      have hn' : r'.end.val-r'.start.val=n := by
        change r.end.val-(r.start.val+1)=n; omega
      rw [SamplerObservedSource.challenge_secure_circle_point_loop,loop_unfold]
      simp only [SamplerObservedSource.challenge_secure_circle_point_loop.body,
        range_next,dif_pos hr,bind_apply,lift_apply,bind_tc_ok,bounded]
      cases hs : SamplerObservedSource.challenge_qm31 s history with
      | fail e => simp
      | div => simp
      | ok pair =>
          rcases pair with ⟨⟨result,s1⟩,observed⟩
          cases result with
          | Err e =>
              simp [map_error,core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                map_apply,lift_apply,pure_apply]
          | Ok t =>
              simp only [bind_tc_ok,map_error,bind_apply,lift_apply,
                core.result.Result.Insts.CoreOpsTry.branch]
              cases hp : circle.secure_ood_circle_point_from_parameter t with
              | fail e => simp
              | div => simp
              | ok result =>
                  cases result with
                  | Ok p => simp [pure_apply]
                  | Err e =>
                      simp only [bind_tc_ok,pure_apply]
                      simpa only [SamplerObservedSource.challenge_secure_circle_point_loop,
                        SamplerObservedSource.challenge_secure_circle_point_loop.body,
                        range_next,map_error,core.result.Result.Insts.CoreOpsTry.branch,
                        r'] using ih r' s1 hn' observed

theorem entry_three (s : transcript.Transcript) (history : Trace) :
    SamplerObservedSource.challenge_secure_circle_point s history = bounded 3 s history := by
  apply loop_execution
  simp only [transcript.CIRCLE_POINT_RETRY_LIMIT]
  rfl

#print axioms loop_execution
#print axioms entry_three
end AspisV8R19.SamplerObservedCircleLoop

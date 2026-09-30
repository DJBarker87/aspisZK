import AspisV8R19.R137SamplerChallengeBridge
import AspisV8R19.SamplerOuterExecution

/-! Exact finite unfolding of the R137 three-attempt nonzero wrapper.  The
inner challenge remains the exact source function proved in the preceding
bridge. -/
set_option autoImplicit false
namespace AspisV8R19.R137NonzeroLoop

open Aeneas Aeneas.Std Result ControlFlow AspisR137Transcript

abbrev Output :=
  (core.result.Result field.QM31 transcript.ChallengeSampleExhausted) ×
    transcript.Transcript

def bounded : Nat → transcript.Transcript → Result Output
  | 0, s => .ok (.Err (), s)
  | n + 1, s => do
      let (r, s1) ← transcript.Transcript.challenge_qm31 s
      match r with
      | .Err _ => .ok (.Err (), s1)
      | .Ok value =>
          let nonzero ← core.cmp.PartialEq.ne.trait_default
            field.QM31.Insts.CoreCmpPartialEqQM31 value field.QM31.ZERO
          if nonzero then .ok (.Ok value, s1) else bounded n s1

theorem body_exhausted (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (h : ¬ r.start.val < r.end.val) :
    transcript.Transcript.challenge_nonzero_qm31_loop.body r s =
      .ok (.done (.Err (), s)) := by
  simp only [transcript.Transcript.challenge_nonzero_qm31_loop.body,
    SamplerOuterExecution.range_next, dif_neg h, bind_tc_ok]

theorem loop_execution (n : Nat) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (hn : r.end.val - r.start.val = n) :
    transcript.Transcript.challenge_nonzero_qm31_loop r s = bounded n s := by
  induction n generalizing r s with
  | zero =>
      have h : ¬ r.start.val < r.end.val := by omega
      rw [transcript.Transcript.challenge_nonzero_qm31_loop, loop.eq_def]
      simp only [body_exhausted r s h, bounded]
  | succ n ih =>
      have h : r.start.val < r.end.val := by omega
      let r' : core.ops.range.Range U32 :=
        { start := UScalar.ofNatCore (r.start.val + 1)
            (by have := r.end.hBounds; omega), «end» := r.end }
      have hn' : r'.end.val - r'.start.val = n := by
        change r.end.val - (r.start.val + 1) = n
        omega
      rw [transcript.Transcript.challenge_nonzero_qm31_loop, loop.eq_def]
      simp only [transcript.Transcript.challenge_nonzero_qm31_loop.body,
        SamplerOuterExecution.range_next, dif_pos h, bind_tc_ok, bounded]
      cases hs : transcript.Transcript.challenge_qm31 s with
      | fail e => simp
      | div => simp
      | ok pair =>
          rcases pair with ⟨result, s1⟩
          cases result with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          | Ok value =>
              simp only [bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch]
              cases hnz : core.cmp.PartialEq.ne.trait_default
                  field.QM31.Insts.CoreCmpPartialEqQM31 value
                  field.QM31.ZERO with
              | fail e => simp
              | div => simp
              | ok nonzero =>
                  cases nonzero with
                  | true => simp
                  | false =>
                      simp only [bind_tc_ok, Bool.false_eq_true, if_false]
                      simpa only [
                        transcript.Transcript.challenge_nonzero_qm31_loop,
                        transcript.Transcript.challenge_nonzero_qm31_loop.body,
                        SamplerOuterExecution.range_next,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok, r']
                        using ih r' s1 hn'

theorem entry_three (s : transcript.Transcript) :
    transcript.Transcript.challenge_nonzero_qm31 s = bounded 3 s := by
  apply loop_execution
  simp only [transcript.NONZERO_QM31_RETRY_LIMIT]
  rfl

#print axioms body_exhausted
#print axioms loop_execution
#print axioms entry_three

end AspisV8R19.R137NonzeroLoop

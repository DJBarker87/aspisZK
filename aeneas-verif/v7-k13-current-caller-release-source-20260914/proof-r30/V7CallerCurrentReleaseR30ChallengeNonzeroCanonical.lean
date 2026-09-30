import V7CallerCurrentReleaseR30ChallengeCanonical

/-!
# Canonicality of successful nonzero transcript challenges

The nonzero sampler retries the ordinary QM31 sampler and only returns one
of its successful values.  This proof follows the exact retry trace and then
lifts the result through the challenge-binding wrapper used for V7 gamma.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30ChallengeNonzeroCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR30ChallengeCanonical

abbrev Transcript := transcript.Transcript
abbrev NonzeroState := core.ops.range.Range Std.U32 × Transcript
abbrev NonzeroOutput :=
  core.result.Result field.QM31 transcript.ChallengeSampleExhausted ×
    Transcript

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem branch_eq_ok_of_continue {Value Error : Type}
    (result : core.result.Result Value Error) (value : Value)
    (success : core.result.Result.Insts.CoreOpsTry.branch result =
      ok (.Continue value)) :
    result = .Ok value := by
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at success ⊢
  exact success

def nonzeroBody (state : NonzeroState) :
    Result (ControlFlow NonzeroState NonzeroOutput) :=
  transcript.Transcript.impl.challenge_nonzero_qm31_loop.body
    state.1 state.2

private theorem done_nonzero_success_canonical
    (state : NonzeroState) (value : field.QM31) (selfOut : Transcript)
    (edge : nonzeroBody state = ok (done (.Ok value, selfOut))) :
    GeneratedCanonicalQM31 value := by
  rcases state with ⟨iter, self⟩
  unfold nonzeroBody at edge
  unfold transcript.Transcript.impl.challenge_nonzero_qm31_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iterAfter⟩
  cases option with
  | none => simp at edge
  | some retryIndex =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨challengePair, challengeRun, edge⟩ := edge
      rcases challengePair with ⟨challengeResult, selfAfter⟩
      rw [bind_eq_ok_iff] at edge
      obtain ⟨flow, branchRun, edge⟩ := edge
      cases flow with
      | Continue sampled =>
          have challengeExact := branch_eq_ok_of_continue challengeResult
            sampled branchRun
          rw [bind_eq_ok_iff] at edge
          obtain ⟨distinct, distinctRun, edge⟩ := edge
          cases distinct with
          | false => cases edge
          | true =>
              have outputExact := ControlFlow.done.inj (Result.ok.inj edge)
              simp only [Prod.mk.injEq, core.result.Result.Ok.injEq]
                at outputExact
              rw [challengeExact] at challengeRun
              rw [← outputExact.1]
              exact successful_challenge_qm31_canonical self selfAfter sampled
                challengeRun
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at edge

private theorem exact_nonzero_trace_success_canonical
    {state : NonzeroState} {output : NonzeroOutput}
    (trace : ExactLoopTrace nonzeroBody state output)
    (value : field.QM31) (selfOut : Transcript)
    (outputExact : output = (.Ok value, selfOut)) :
    GeneratedCanonicalQM31 value := by
  induction trace with
  | done edge =>
      rw [outputExact] at edge
      exact done_nonzero_success_canonical _ value selfOut edge
  | cont edge tail inductionHypothesis =>
      exact inductionHypothesis outputExact

theorem successful_challenge_nonzero_qm31_canonical
    (self selfOut : Transcript) (value : field.QM31)
    (run : transcript.Transcript.impl.challenge_nonzero_qm31 self =
      ok (.Ok value, selfOut)) :
    GeneratedCanonicalQM31 value := by
  unfold transcript.Transcript.impl.challenge_nonzero_qm31 at run
  unfold transcript.Transcript.impl.challenge_nonzero_qm31_loop at run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace nonzeroBody
    ({ start := 0#u32,
       «end» := transcript.NONZERO_QM31_RETRY_LIMIT }, self)
    (.Ok value, selfOut) run
  exact exact_nonzero_trace_success_canonical trace value selfOut rfl

theorem successful_challenge_nonzero_qm31_bound_canonical
    (self selfOut : Transcript) (challengeId : Std.U8)
    (value : field.QM31)
    (run : transcript.Transcript.impl.challenge_nonzero_qm31_bound self
      challengeId = ok (.Ok value, selfOut)) :
    GeneratedCanonicalQM31 value := by
  unfold transcript.Transcript.impl.challenge_nonzero_qm31_bound at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨challengePair, challengeRun, run⟩ := run
  rcases challengePair with ⟨challengeResult, selfAfter⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨flow, branchRun, run⟩ := run
  cases flow with
  | Continue sampled =>
      have challengeExact := branch_eq_ok_of_continue challengeResult sampled
        branchRun
      rw [challengeExact] at challengeRun
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨boundTranscript, bindRun, run⟩ := run
      have outputExact := Result.ok.inj run
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at outputExact
      rw [← outputExact.1]
      exact successful_challenge_nonzero_qm31_canonical self selfAfter sampled
        challengeRun
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run

#print axioms successful_challenge_nonzero_qm31_canonical
#print axioms successful_challenge_nonzero_qm31_bound_canonical

end V7CallerCurrentReleaseR30ChallengeNonzeroCanonical

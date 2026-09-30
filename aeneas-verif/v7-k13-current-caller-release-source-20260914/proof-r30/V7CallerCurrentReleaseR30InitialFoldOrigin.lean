import V7CallerCurrentReleaseR30CircleAccumulator
import V7CallerCurrentReleaseR26WeightFoldLoopTrace
import V7CallerCurrentReleaseR30ChallengeCanonical

/-!
# Exact initial deferred-fold extraction

The successful terminal branch of the current circle loop evaluates the
first relation polynomial and runs the literal first arity-four weight fold.
This module retains that source call, then exposes its existing symbolic fold
trace without reducing the generated recurrence.
-/
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30InitialFoldOrigin

open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR26AcceptedCircleExhausted
open V7CallerCurrentReleaseR26AcceptedOuterLoop
open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR30ChallengeCanonical

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator

private theorem initial_alpha_read_exact
    (sampledAlpha alpha : RawQM31) (values : Array RawQM31 4#usize)
    (updateRun : Array.update (Array.repeat 4#usize field.QM31.ZERO)
      0#usize sampledAlpha = ok values)
    (readRun : Array.index_usize values 0#usize = ok alpha) :
    alpha = sampledAlpha := by
  simp [Array.update, Array.index_usize] at updateRun readRun
  subst values
  simpa using readRun.symm

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem branch_eq_ok_of_continue {Value Error : Type}
    (result : core.result.Result Value Error) (value : Value)
    (success : core.result.Result.Insts.CoreOpsTry.branch result =
      .ok (.Continue value)) :
    result = .Ok value := by
  cases result with
  | Ok actual =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using success
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at success

theorem successful_challenge_qm31_bound_canonical
    (self selfOut : transcript.Transcript) (challengeId : Std.U8)
    (value : RawQM31)
    (run : transcript.Transcript.impl.challenge_qm31_bound self challengeId =
      ok (.Ok value, selfOut)) :
    GeneratedCanonicalQM31 value := by
  unfold transcript.Transcript.impl.challenge_qm31_bound at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨challengePair, challengeRun, run⟩ := run
  rcases challengePair with ⟨challengeResult, selfAfterChallenge⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨challengeFlow, challengeFlowRun, run⟩ := run
  cases challengeFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Continue sampled =>
      have challengeExact := branch_eq_ok_of_continue challengeResult sampled
        challengeFlowRun
      rw [bind_eq_ok_iff] at run
      obtain ⟨selfAfterBind, _, run⟩ := run
      have outputExact : (core.result.Result.Ok sampled, selfAfterBind) =
          (core.result.Result.Ok value, selfOut) :=
        Result.ok.inj run
      have sampledExact : sampled = value :=
        core.result.Result.Ok.inj (congrArg Prod.fst outputExact)
      rw [challengeExact, sampledExact] at challengeRun
      exact successful_challenge_qm31_canonical self selfAfterChallenge value
        challengeRun

structure AcceptedInitialFold {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) : Type where
  alpha : RawQM31
  sampledAlpha : RawQM31
  transcriptBeforeSample : transcript.Transcript
  transcriptAfterSample : transcript.Transcript
  sampleRun : transcript.Transcript.impl.challenge_qm31_bound
    transcriptBeforeSample transcript.V7_ALPHA_ZERO_BIND_ID =
      ok (.Ok sampledAlpha, transcriptAfterSample)
  alphaExact : alpha = sampledAlpha
  weights : RawWeights
  foldRun : sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4
    origin.state.2.2.2.2 alpha = ok weights

theorem AcceptedInitialFold.alpha_canonical
    {circle : AcceptedCircleLoopDispatch outer}
    {origin : AcceptedCircleBodyOrigin circle}
    (first : AcceptedInitialFold origin) :
    GeneratedCanonicalQM31 first.alpha := by
  rw [first.alphaExact]
  exact successful_challenge_qm31_bound_canonical first.transcriptBeforeSample
    first.transcriptAfterSample transcript.V7_ALPHA_ZERO_BIND_ID
    first.sampledAlpha first.sampleRun

theorem AcceptedCircleBodyOrigin.exposesInitialFold
    {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) :
    Nonempty (AcceptedInitialFold origin) := by
  obtain ⟨iterNext, iteratorExhausted⟩ :=
    V7CallerCurrentReleaseR26AcceptedCircleExhausted.AcceptedCircleBodyOrigin.iteratorExhausted
      origin
  have run := origin.bodyRun
  unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨iteratorPair, iteratorRun, run⟩ := run
  rw [iteratorExhausted] at iteratorRun
  have iteratorPairExact : iteratorPair = (none, iterNext) := by
    simpa using iteratorRun.symm
  subst iteratorPair
  simp only at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨traceCirclePair, _, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨relationPair, relationRun, run⟩ := run
  rcases relationPair with ⟨relationResult, fieldsAfterRelation⟩
  rw [bind_eq_ok_iff] at run
  obtain ⟨relationFlow, relationBranch, run⟩ := run
  cases relationFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Continue relationFields =>
      have relationExact := branch_eq_ok_of_continue relationResult
        relationFields relationBranch
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨traceRelationPair, _, run⟩ := run
      rcases traceRelationPair with ⟨_, traceAfterRelation⟩
      rw [bind_eq_ok_iff] at run
      obtain ⟨firstEncoded, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨firstPolynomial, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨transcriptAfterPolynomial, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldNonce, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldBits, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldCheckPair, _, run⟩ := run
      rcases foldCheckPair with ⟨foldCheckResult, transcriptAfterFoldWork⟩
      rw [bind_eq_ok_iff] at run
      obtain ⟨foldCheckFlow, _, run⟩ := run
      cases foldCheckFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
      | Continue _foldUnit =>
          simp only [↓reduceIte] at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaChallengePair, alphaChallengePairRun, run⟩ := run
          rcases alphaChallengePair with
            ⟨alphaChallengeResult, transcriptAfterAlpha⟩
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaSwapped, alphaSwappedRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaMapped, alphaMappedRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaFlow, alphaFlowRun, run⟩ := run
          cases alphaFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at run
          | Continue alphaZero =>
              have alphaMappedExact := branch_eq_ok_of_continue alphaMapped
                alphaZero alphaFlowRun
              have alphaSwappedExact : alphaSwapped =
                  (transcriptAfterAlpha, alphaChallengeResult) :=
                Result.ok.inj alphaSwappedRun.symm
              subst alphaSwapped
              have alphaChallengeExact : alphaChallengeResult = .Ok alphaZero := by
                rw [alphaMappedExact] at alphaMappedRun
                cases alphaChallengeResult with
                | Ok actual =>
                    have actualExact : actual = alphaZero := by
                      simpa [core.result.Result.map_err] using alphaMappedRun
                    subst actual
                    rfl
                | Err error =>
                    simp [core.result.Result.map_err,
                      v6_transcript.finish_onefold_relation.closure_7.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once]
                      at alphaMappedRun
              have sampleRun :
                  transcript.Transcript.impl.challenge_qm31_bound
                      transcriptAfterFoldWork transcript.V7_ALPHA_ZERO_BIND_ID =
                    ok (.Ok alphaZero, transcriptAfterAlpha) := by
                rw [alphaChallengeExact] at alphaChallengePairRun
                exact alphaChallengePairRun
              rw [bind_eq_ok_iff] at run
              obtain ⟨alpha, alphaUpdateRun, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨alphaZeroRead, alphaZeroReadRun, run⟩ := run
              have alphaExact := initial_alpha_read_exact alphaZero
                alphaZeroRead alpha alphaUpdateRun alphaZeroReadRun
              rw [bind_eq_ok_iff] at run
              obtain ⟨runningClaim, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨weights, foldRun, run⟩ := run
              exact ⟨⟨alphaZeroRead, alphaZero, transcriptAfterFoldWork,
                transcriptAfterAlpha, sampleRun, alphaExact, weights, foldRun⟩⟩

theorem AcceptedCircleBodyOrigin.exposesInitialFoldTrace
    {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) :
    Nonempty (Σ first : AcceptedInitialFold origin,
      FirstDeferredFoldTrace origin.state.2.2.2.2 first.alpha first.weights) := by
  obtain ⟨first⟩ := exposesInitialFold origin
  obtain ⟨trace⟩ := first_deferred_fold_exposes_exact_trace first.foldRun
  exact ⟨⟨first, trace⟩⟩

#print axioms AcceptedCircleBodyOrigin.exposesInitialFold
#print axioms AcceptedCircleBodyOrigin.exposesInitialFoldTrace
#print axioms AcceptedInitialFold.alpha_canonical
end V7CallerCurrentReleaseR30InitialFoldOrigin

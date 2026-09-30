import V7CallerCurrentReleaseR30CircleAccumulator
import V7CallerCurrentReleaseR26WeightFoldLoopTrace

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

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator

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

structure AcceptedInitialFold {circle : AcceptedCircleLoopDispatch outer}
    (origin : AcceptedCircleBodyOrigin circle) : Type where
  alpha : RawQM31
  weights : RawWeights
  foldRun : sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4
    origin.state.2.2.2.2 alpha = ok weights

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
          obtain ⟨alphaChallengePair, _, run⟩ := run
          rcases alphaChallengePair with
            ⟨alphaChallengeResult, transcriptAfterAlpha⟩
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaSwapped, _, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaMapped, _, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alphaFlow, _, run⟩ := run
          cases alphaFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at run
          | Continue alphaZero =>
              rw [bind_eq_ok_iff] at run
              obtain ⟨alpha, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨alphaZeroRead, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨runningClaim, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨weights, foldRun, run⟩ := run
              exact ⟨⟨alphaZeroRead, weights, foldRun⟩⟩

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
end V7CallerCurrentReleaseR30InitialFoldOrigin

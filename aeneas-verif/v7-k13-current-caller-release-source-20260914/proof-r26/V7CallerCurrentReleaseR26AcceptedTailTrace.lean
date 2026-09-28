import V7CallerCurrentReleaseR26AcceptedTailSnapshot

/-!
# Exact current-source relation-loop trace

This file retains every literal body equation from a successful execution of
the current generated relation loop.  Subsequent lemmas invert its three
fixed continuation edges and terminal edge into the maintained accepted-tail
source record.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTailTrace

universe u v

/-- A finite sequence of equations for the literal generated loop body. -/
inductive ExactLoopTrace {State : Type u} {Output : Type v}
    (body : State → Result (ControlFlow State Output)) :
    State → Output → Type (max u v)
  | done {state output}
      (equation : body state = .ok (.done output)) :
      ExactLoopTrace body state output
  | cont {state next output}
      (equation : body state = .ok (.cont next))
      (tail : ExactLoopTrace body next output) :
      ExactLoopTrace body state output

def ExactLoopTrace.contCount
    {State : Type u} {Output : Type v}
    {body : State → Result (ControlFlow State Output)}
    {state : State} {output : Output} :
    ExactLoopTrace body state output → Nat
  | .done _ => 0
  | .cont _ tail => tail.contCount + 1

/-- Partial-correctness inversion of Aeneas's exact fixpoint.  Successful
execution produces a finite chain of body equations without a totality
assumption. -/
theorem loop_success_yields_exact_trace
    {State Output : Type*}
    (body : State → Result (ControlFlow State Output)) :
    ∀ state output, loop body state = .ok output →
      Nonempty (ExactLoopTrace body state output) := by
  apply loop.fixpoint_induct body
    (motive := fun recursive => ∀ state output,
      recursive state = .ok output →
        Nonempty (ExactLoopTrace body state output))
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_pi
    intro output
    apply Lean.Order.admissible_apply
      (β := fun _ : State => Result Output)
      (P := fun _ computation => computation = Result.ok output →
        Nonempty (ExactLoopTrace body state output))
      state
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recursive inductionHypothesis state output run
    simp only at run
    cases bodyEquation : body state with
    | fail error => simp [bodyEquation] at run
    | div => simp [bodyEquation] at run
    | ok flow =>
        cases flow with
        | cont next =>
            have recursiveRun : recursive next = .ok output := by
              simpa [bodyEquation] using run
            let tail := Classical.choice
              (inductionHypothesis next output recursiveRun)
            exact ⟨ExactLoopTrace.cont bodyEquation tail⟩
        | done bodyOutput =>
            have outputExact : bodyOutput = output := by
              simpa [bodyEquation] using run
            subst output
            exact ⟨ExactLoopTrace.done bodyEquation⟩

/-- Every accepted current generated relation loop exposes every body edge
that led to its result. -/
theorem accepted_relation_loop_has_exact_trace
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (iter : core.ops.range.Range Std.Usize)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (gamma runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    (success :
      v6_transcript.finish_onefold_relation_after_prechallenge_loop
        queryFoldInst traceInst iter transcript0 trace0 gamma runningClaim
        weights alpha foldedValues relationFields selector semanticPoint kappa
        queries compactCounter frontierNodes transcriptStateAfterQueries
        snapshot queryBatchChallenge authenticatedQueries =
          ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    Nonempty (ExactLoopTrace
      (V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries)
      (iter, transcript0, trace0, runningClaim, weights, alpha, foldedValues)
      (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) := by
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop at success
  let body :=
    V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
      traceInst gamma relationFields selector semanticPoint kappa queries
      compactCounter frontierNodes transcriptStateAfterQueries snapshot
      queryBatchChallenge authenticatedQueries
  have bodyEq :
      (fun (iter1, transcript1, trace1, runningClaim1, weights1, alpha1,
          foldedValues1) =>
        v6_transcript.finish_onefold_relation_after_prechallenge_loop.body
          queryFoldInst traceInst gamma relationFields selector semanticPoint
          kappa queries compactCounter frontierNodes
          transcriptStateAfterQueries snapshot queryBatchChallenge
          authenticatedQueries iter1 transcript1 trace1 runningClaim1 weights1
          alpha1 foldedValues1) = body := by
    funext state
    rcases state with
      ⟨iter1, transcript1, trace1, runningClaim1, weights1, alpha1,
        foldedValues1⟩
    rfl
  rw [bodyEq] at success
  exact loop_success_yields_exact_trace body
    (iter, transcript0, trace0, runningClaim, weights, alpha, foldedValues)
    (core.result.Result.Ok (verified, returnedSnapshot), traceOut) success

theorem range_next_some_exact
    (iter iter' : core.ops.range.Range Std.Usize) (round : Std.Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some round, iter')) :
    iter.start.val < iter.end.val ∧ round = iter.start ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  have active : iter.start.val < iter.end.val := by
    by_contra notActive
    have finished : iter.end.val ≤ iter.start.val := by omega
    have spec := core.iter.range.IteratorRange.next_Usize_none_spec iter
      finished
    rcases Aeneas.Std.WP.spec_imp_exists spec with
      ⟨⟨option, stopped⟩, stoppedRun, optionNone, stoppedEq⟩
    have outputs := Result.ok.inj (stoppedRun.symm.trans run)
    have options := congrArg Prod.fst outputs
    simp [optionNone] at options
  have spec := core.iter.range.IteratorRange.next_Usize_some_spec iter active
  rcases Aeneas.Std.WP.spec_imp_exists spec with
    ⟨⟨option, advanced⟩, advancedRun, optionEq, startEq, endEq⟩
  have outputs := Result.ok.inj (advancedRun.symm.trans run)
  have options := congrArg Prod.fst outputs
  have iterators := congrArg Prod.snd outputs
  have roundEq : round = iter.start := by
    simpa [optionEq] using options.symm
  have advancedEq : iter' = advanced := iterators.symm
  exact ⟨active, roundEq,
    advancedEq ▸ startEq,
    advancedEq ▸ endEq⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- A continuation edge of the literal tail body can only come from the
active iterator branch, and its successor carries the iterator returned by
that exact `next` call. -/
theorem tail_body_cont_iterator_step
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (gamma : field.QM31)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (state nextState :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace)
    (run :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries state = ok (cont nextState)) :
    ∃ round iter',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
          ok (some round, iter') ∧
        nextState.1 = iter' := by
  unfold V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody at run
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨iteratorPair, iteratorRun, run⟩ := run
  rcases iteratorPair with ⟨option, iter'⟩
  cases option with
  | none =>
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨slice, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨terminalDot, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨terminalMismatch, _, run⟩ := run
      by_cases mismatch : terminalMismatch = true
      · simp [mismatch] at run
      · simp [mismatch] at run
        rw [bind_eq_ok_iff] at run
        obtain ⟨tracePair, _, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨queryIter, _, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨foldedQuerySum, _, run⟩ := run
        cases run
  | some round =>
      refine ⟨round, iter', iteratorRun, ?_⟩
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨relationRow, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨polynomial, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨transcript1, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨challengePair, _, run⟩ := run
      rcases challengePair with ⟨challengeResult, transcript2⟩
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨mappedChallenge, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨flow, _, run⟩ := run
      cases flow with
      | Break residual =>
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨residualResult, residualRun, run⟩ := run
          cases residual with
          | Ok impossible => cases impossible
          | Err error =>
              simp only [
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from, bind_tc_ok,
                Aeneas.Std.Result.ok.injEq] at residualRun
              subst residualResult
              cases run
      | Continue challenge =>
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alpha1, _, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨roundChallenge, _, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨runningClaim1, _, run⟩ := run
          split at run <;> simp only [bind_tc_ok] at run
          all_goals
            rw [bind_eq_ok_iff] at run
            obtain ⟨polynomialTrace, _, run⟩ := run
            rw [bind_eq_ok_iff] at run
            obtain ⟨lastRound, _, run⟩ := run
            by_cases isLast : round = lastRound
            · simp only [isLast, ↓reduceIte] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨q1, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨q2, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨q3, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨foldPair, _, run⟩ := run
              by_cases folded : foldPair.1 = true
              · simp only [folded, ↓reduceIte] at run
                try simp only [bind_tc_ok, *] at run
                rw [bind_eq_ok_iff] at run
                obtain ⟨weightsTrace, _, run⟩ := run
                rw [bind_eq_ok_iff] at run
                obtain ⟨foldedValues1, _, run⟩ := run
                try simp only [bind_tc_ok, *] at run
                rw [bind_eq_ok_iff] at run
                obtain ⟨roundTrace, _, run⟩ := run
                first
                  | exact congrArg
                      (fun next :
                        V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace =>
                          next.1)
                      (ControlFlow.cont.inj (Result.ok.inj run).symm)
                  | (rw [bind_eq_ok_iff] at run
                     obtain ⟨roundTracePair, _, run⟩ := run
                     exact congrArg
                      (fun next :
                        V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace =>
                          next.1)
                      (ControlFlow.cont.inj (Result.ok.inj run).symm))
              · simp [folded] at run
            · simp only [isLast, ↓reduceIte] at run
              try simp only [bind_tc_ok, *] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨weightsTrace, _, run⟩ := run
              try simp only [bind_tc_ok, *] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨foldedValues1, _, run⟩ := run
              try simp only [bind_tc_ok, *] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨roundTrace, _, run⟩ := run
              first
                | exact congrArg
                    (fun next :
                      V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace =>
                        next.1)
                    (ControlFlow.cont.inj (Result.ok.inj run).symm)
                | (rw [bind_eq_ok_iff] at run
                   obtain ⟨roundTracePair, _, run⟩ := run
                   exact congrArg
                    (fun next :
                      V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace =>
                        next.1)
                    (ControlFlow.cont.inj (Result.ok.inj run).symm))

theorem range_next_none_exhausted
    (iter iter' : core.ops.range.Range Std.Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter')) :
    iter.end.val ≤ iter.start.val := by
  by_contra notFinished
  have active : iter.start.val < iter.end.val := by omega
  have spec := core.iter.range.IteratorRange.next_Usize_some_spec iter active
  rcases Aeneas.Std.WP.spec_imp_exists spec with
    ⟨⟨option, advanced⟩, advancedRun, optionEq, _, _⟩
  have outputs := Result.ok.inj (advancedRun.symm.trans run)
  have options := congrArg Prod.fst outputs
  simp [optionEq] at options

/-- An accepted `done` edge of the literal body can only come from the
exhausted iterator branch. -/
theorem tail_body_accepted_done_iterator_none
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (gamma : field.QM31)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (state : V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    (run :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries state =
          ok (done (core.result.Result.Ok (verified, returnedSnapshot),
            traceOut))) :
    ∃ iter',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        ok (none, iter') := by
  unfold V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody at run
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨iteratorPair, iteratorRun, run⟩ := run
  rcases iteratorPair with ⟨option, iter'⟩
  cases option with
  | none => exact ⟨iter', iteratorRun⟩
  | some round =>
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨relationRow, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨polynomial, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨transcript1, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨challengePair, _, run⟩ := run
      rcases challengePair with ⟨challengeResult, transcript2⟩
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨mappedChallenge, _, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨flow, _, run⟩ := run
      cases flow with
      | Break residual =>
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨residualResult, residualRun, run⟩ := run
          cases residual with
          | Ok impossible => cases impossible
          | Err error =>
              simp only [
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from, bind_tc_ok,
                Aeneas.Std.Result.ok.injEq] at residualRun
              subst residualResult
              cases run
      | Continue challenge =>
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨alpha1, _, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨roundChallenge, _, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨runningClaim1, _, run⟩ := run
          split at run <;> simp only [bind_tc_ok] at run
          all_goals
            rw [bind_eq_ok_iff] at run
            obtain ⟨polynomialTrace, _, run⟩ := run
            rw [bind_eq_ok_iff] at run
            obtain ⟨lastRound, _, run⟩ := run
            by_cases isLast : round = lastRound
            · simp only [isLast, ↓reduceIte] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨q1, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨q2, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨q3, _, run⟩ := run
              rw [bind_eq_ok_iff] at run
              obtain ⟨foldPair, _, run⟩ := run
              by_cases folded : foldPair.1 = true
              · simp only [folded, ↓reduceIte] at run
                try simp only [bind_tc_ok, *] at run
                rw [bind_eq_ok_iff] at run
                obtain ⟨weightsTrace, _, run⟩ := run
                rw [bind_eq_ok_iff] at run
                obtain ⟨foldedValues1, _, run⟩ := run
                try simp only [bind_tc_ok, *] at run
                rw [bind_eq_ok_iff] at run
                obtain ⟨roundTrace, _, run⟩ := run
                first
                  | cases run
                  | (rw [bind_eq_ok_iff] at run
                     obtain ⟨roundTracePair, _, run⟩ := run
                     cases run)
              · simp only [folded] at run
                cases run
            · simp only [isLast, ↓reduceIte] at run
              try simp only [bind_tc_ok, *] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨weightsTrace, _, run⟩ := run
              try simp only [bind_tc_ok, *] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨foldedValues1, _, run⟩ := run
              try simp only [bind_tc_ok, *] at run
              rw [bind_eq_ok_iff] at run
              obtain ⟨roundTrace, _, run⟩ := run
              first
                | cases run
                | (rw [bind_eq_ok_iff] at run
                   obtain ⟨roundTracePair, _, run⟩ := run
                   cases run)

/-- The trace length is determined by the range carried in the source state.
This is a symbolic iterator argument; it never unfolds a large recurrence. -/
private theorem exact_trace_contCount_eq_remaining
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (gamma : field.QM31)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    {state : V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace}
    (execution : ExactLoopTrace
      (V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries)
      state (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    execution.contCount = state.1.2.val - state.1.1.val := by
  cases execution with
  | done equation =>
      obtain ⟨iter', iteratorRun⟩ := tail_body_accepted_done_iterator_none
        queryFoldInst traceInst gamma relationFields selector semanticPoint
        kappa queries compactCounter frontierNodes transcriptStateAfterQueries
        snapshot queryBatchChallenge authenticatedQueries state verified
        returnedSnapshot traceOut equation
      have exhausted := range_next_none_exhausted state.1 iter' iteratorRun
      simp [ExactLoopTrace.contCount, Nat.sub_eq_zero_of_le exhausted]
  | @cont state next _ equation tail =>
      have inductionHypothesis := exact_trace_contCount_eq_remaining
        queryFoldInst traceInst gamma relationFields selector semanticPoint
        kappa queries compactCounter frontierNodes transcriptStateAfterQueries
        snapshot queryBatchChallenge authenticatedQueries verified
        returnedSnapshot traceOut tail
      obtain ⟨round, iter', iteratorRun, nextIterator⟩ :=
        tail_body_cont_iterator_step queryFoldInst traceInst gamma
          relationFields selector semanticPoint kappa queries compactCounter
          frontierNodes transcriptStateAfterQueries snapshot
          queryBatchChallenge authenticatedQueries state next equation
      obtain ⟨active, _, nextStart, sameEnd⟩ :=
        range_next_some_exact state.1 iter' round iteratorRun
      rw [nextIterator] at inductionHypothesis
      simp only [ExactLoopTrace.contCount]
      rw [inductionHypothesis, sameEnd, nextStart]
      omega
termination_by execution.contCount
decreasing_by
  simp_all [ExactLoopTrace.contCount]

/-- The exact four body equations of an accepted current-source relation
tail.  The first three are the fixed rounds 1, 2, and 3; the fourth is the
terminal comparison and accepted return. -/
structure ThreeRoundAcceptedTailExecution
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (gamma : field.QM31)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (initial : V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace) : Type where
  afterOne : V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace
  afterTwo : V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace
  afterThree : V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace
  roundOne :
    V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
      traceInst gamma relationFields selector semanticPoint kappa queries
      compactCounter frontierNodes transcriptStateAfterQueries snapshot
      queryBatchChallenge authenticatedQueries initial = ok (cont afterOne)
  roundTwo :
    V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
      traceInst gamma relationFields selector semanticPoint kappa queries
      compactCounter frontierNodes transcriptStateAfterQueries snapshot
      queryBatchChallenge authenticatedQueries afterOne = ok (cont afterTwo)
  roundThree :
    V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
      traceInst gamma relationFields selector semanticPoint kappa queries
      compactCounter frontierNodes transcriptStateAfterQueries snapshot
      queryBatchChallenge authenticatedQueries afterTwo = ok (cont afterThree)
  terminal :
    V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
      traceInst gamma relationFields selector semanticPoint kappa queries
      compactCounter frontierNodes transcriptStateAfterQueries snapshot
      queryBatchChallenge authenticatedQueries afterThree =
        ok (done (core.result.Result.Ok (verified, returnedSnapshot), traceOut))

/-- A successful literal loop started at `1..4` consists of exactly the
three relation rounds and its accepted terminal edge. -/
theorem accepted_relation_loop_has_three_round_execution
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (gamma runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    (success :
      v6_transcript.finish_onefold_relation_after_prechallenge_loop
        queryFoldInst traceInst
        { start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS }
        transcript0 trace0 gamma runningClaim weights alpha foldedValues
        relationFields selector semanticPoint kappa queries compactCounter
        frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
        authenticatedQueries =
          ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    Nonempty (ThreeRoundAcceptedTailExecution queryFoldInst traceInst gamma
      relationFields selector semanticPoint kappa queries compactCounter
      frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries
      ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS },
        transcript0, trace0, runningClaim, weights, alpha, foldedValues)
      verified returnedSnapshot traceOut) := by
  obtain ⟨execution⟩ := accepted_relation_loop_has_exact_trace
    queryFoldInst traceInst
    { start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS }
    transcript0 trace0 gamma runningClaim weights alpha foldedValues
    relationFields selector semanticPoint kappa queries compactCounter
    frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
    authenticatedQueries verified returnedSnapshot traceOut success
  have count : execution.contCount = 3 := by
    have remaining := exact_trace_contCount_eq_remaining queryFoldInst traceInst
      gamma relationFields selector semanticPoint kappa queries compactCounter
      frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries verified returnedSnapshot traceOut execution
    simpa [v6_onefold.V6_RELATION_ROUNDS] using remaining
  cases execution with
  | done equation => simp [ExactLoopTrace.contCount] at count
  | @cont _ afterOne _ roundOne tailOne =>
      cases tailOne with
      | done equation => simp [ExactLoopTrace.contCount] at count
      | @cont _ afterTwo _ roundTwo tailTwo =>
          cases tailTwo with
          | done equation => simp [ExactLoopTrace.contCount] at count
          | @cont _ afterThree _ roundThree tailThree =>
              cases tailThree with
              | done terminal =>
                  exact ⟨{
                    afterOne := afterOne
                    afterTwo := afterTwo
                    afterThree := afterThree
                    roundOne := roundOne
                    roundTwo := roundTwo
                    roundThree := roundThree
                    terminal := terminal }⟩
              | cont equation tailFour =>
                  simp [ExactLoopTrace.contCount] at count

/-- The four retained body equations are pinned to the literal source
iterator values `1`, `2`, `3`, and then exhaustion. -/
theorem ThreeRoundAcceptedTailExecution.iterator_equations
    {QueryFold Trace : Type}
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (gamma runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    (execution : ThreeRoundAcceptedTailExecution queryFoldInst traceInst gamma
      relationFields selector semanticPoint kappa queries compactCounter
      frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries
      ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS },
        transcript0, trace0, runningClaim, weights, alpha, foldedValues)
      verified returnedSnapshot traceOut) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS } :
          core.ops.range.Range Std.Usize) =
        ok (some 1#usize, execution.afterOne.1) ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          execution.afterOne.1 =
        ok (some 2#usize, execution.afterTwo.1) ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          execution.afterTwo.1 =
        ok (some 3#usize, execution.afterThree.1) ∧
      ∃ terminalIterator,
        core.iter.range.IteratorRange.next core.iter.range.StepUsize
            execution.afterThree.1 = ok (none, terminalIterator) := by
  obtain ⟨roundOne, iterOne, nextOne, afterOneIterator⟩ :=
    tail_body_cont_iterator_step queryFoldInst traceInst gamma relationFields
      selector semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries
      ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS },
        transcript0, trace0, runningClaim, weights, alpha, foldedValues)
      execution.afterOne execution.roundOne
  obtain ⟨_, roundOneStart, nextOneStart, _⟩ :=
    range_next_some_exact
      ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS } :
        core.ops.range.Range Std.Usize)
      iterOne roundOne nextOne
  have roundOneExact : roundOne = 1#usize := by
    simpa using roundOneStart
  have afterOneStart : execution.afterOne.1.1.val = 2 := by
    rw [afterOneIterator]
    simpa using nextOneStart
  obtain ⟨roundTwo, iterTwo, nextTwo, afterTwoIterator⟩ :=
    tail_body_cont_iterator_step queryFoldInst traceInst gamma relationFields
      selector semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries execution.afterOne execution.afterTwo
      execution.roundTwo
  obtain ⟨_, roundTwoStart, nextTwoStart, _⟩ :=
    range_next_some_exact execution.afterOne.1 iterTwo roundTwo nextTwo
  have roundTwoExact : roundTwo = 2#usize := by
    apply UScalar.eq_of_val_eq
    rw [roundTwoStart]
    exact afterOneStart
  have afterTwoStart : execution.afterTwo.1.1.val = 3 := by
    rw [afterTwoIterator]
    have := nextTwoStart
    rw [afterOneStart] at this
    exact this
  obtain ⟨roundThree, iterThree, nextThree, afterThreeIterator⟩ :=
    tail_body_cont_iterator_step queryFoldInst traceInst gamma relationFields
      selector semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries execution.afterTwo execution.afterThree
      execution.roundThree
  obtain ⟨_, roundThreeStart, _, _⟩ :=
    range_next_some_exact execution.afterTwo.1 iterThree roundThree nextThree
  have roundThreeExact : roundThree = 3#usize := by
    apply UScalar.eq_of_val_eq
    rw [roundThreeStart]
    exact afterTwoStart
  obtain ⟨terminalIterator, terminalNext⟩ :=
    tail_body_accepted_done_iterator_none queryFoldInst traceInst gamma
      relationFields selector semanticPoint kappa queries compactCounter
      frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries execution.afterThree verified returnedSnapshot
      traceOut execution.terminal
  refine ⟨?_, ?_, ?_, terminalIterator, terminalNext⟩
  · simpa [roundOneExact, afterOneIterator] using nextOne
  · simpa [roundTwoExact, afterTwoIterator] using nextTwo
  · simpa [roundThreeExact, afterThreeIterator] using nextThree

#print axioms loop_success_yields_exact_trace
#print axioms accepted_relation_loop_has_exact_trace
#print axioms accepted_relation_loop_has_three_round_execution
#print axioms ThreeRoundAcceptedTailExecution.iterator_equations

end V7CallerCurrentReleaseR26AcceptedTailTrace

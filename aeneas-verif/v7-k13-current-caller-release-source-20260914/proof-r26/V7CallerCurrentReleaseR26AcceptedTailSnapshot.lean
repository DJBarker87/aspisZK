import V7CallerCurrentReleaseR26AcceptedTailDispatch

/-!
# Accepted current relation tail preserves its prechallenge snapshot

The proof uses partial fixpoint induction for the literal Aeneas loop. A
successful loop result must originate at one generated `done` body step; the
accepted `done` branch returns the caller's snapshot verbatim.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTailSnapshot

abbrev Snapshot := v6_transcript.V6QueryBatchPrechallengeSnapshot
abbrev TailOutput (Trace : Type) :=
  (core.result.Result
      (v6_transcript.V6VerifiedTranscript × Option Snapshot)
      v6_transcript.V6TranscriptError) × Trace
abbrev TailState (Trace : Type) :=
  core.ops.range.Range Std.Usize × transcript.Transcript × Trace × field.QM31 ×
    sumcheck.WeightAccumulator × Array field.QM31 4#usize ×
    Array field.QM31 256#usize

noncomputable def tailBody {QueryFold Trace : Type}
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
    (snapshot : Option Snapshot) (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (state : TailState Trace) : Result (ControlFlow (TailState Trace)
      (TailOutput Trace)) :=
  v6_transcript.finish_onefold_relation_after_prechallenge_loop.body
    queryFoldInst traceInst gamma relationFields selector semanticPoint kappa
    queries compactCounter frontierNodes transcriptStateAfterQueries snapshot
    queryBatchChallenge authenticatedQueries state.1 state.2.1 state.2.2.1
    state.2.2.2.1 state.2.2.2.2.1 state.2.2.2.2.2.1
    state.2.2.2.2.2.2

def HasDoneOrigin {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (result : Result Output) : Prop :=
  match result with
  | .ok output => ∃ state, body state = .ok (.done output)
  | .fail _ | .div => True

/-- Partial correctness of the Aeneas fixpoint: a successful result was
produced by a literal `done` body equation. No totality premise is used. -/
theorem loop_ok_has_done_origin
    {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (initial : State) :
    HasDoneOrigin body (loop body initial) := by
  generalize initial = state
  revert state
  apply loop.fixpoint_induct
    (motive := fun loop' => ∀ state, HasDoneOrigin body (loop' state))
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_apply
      (fun _ result => HasDoneOrigin body result) state
    apply Lean.Order.admissible_flatOrder
    simp [HasDoneOrigin]
  · intro loop' inductionHypothesis state
    simp only
    cases bodyEquation : body state with
    | div => simp [HasDoneOrigin]
    | fail error => simp [HasDoneOrigin]
    | ok flow =>
        cases flow with
        | done output =>
            simp [HasDoneOrigin]
            exact ⟨state, bodyEquation⟩
        | cont next =>
            simpa [HasDoneOrigin] using inductionHypothesis next

theorem loop_ok_has_done_origin_eq
    {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (initial : State) (output : Output)
    (run : loop body initial = .ok output) :
    ∃ state, body state = .ok (.done output) := by
  have origin := loop_ok_has_done_origin body initial
  simpa [HasDoneOrigin, run] using origin

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- The only generated body branch that can return an accepted verifier
result is the exhausted-iterator terminal branch, which embeds `snapshot`
unchanged in that result. -/
theorem tail_body_accepted_done_preserves_snapshot
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
    (snapshot : Option Snapshot) (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (state : TailState Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot) (traceOut : Trace)
    (run : tailBody queryFoldInst traceInst gamma relationFields selector
      semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries state =
        ok (done (core.result.Result.Ok (verified, returnedSnapshot),
          traceOut))) :
    returnedSnapshot = snapshot := by
  unfold tailBody at run
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨iteratorPair, _, run⟩ := run
  rcases iteratorPair with ⟨option, iter1⟩
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
      · simp only [mismatch, ↓reduceIte] at run
        cases run
      · simp only [mismatch] at run
        simp only [Bool.false_eq_true, ↓reduceIte] at run
        rw [bind_eq_ok_iff] at run
        obtain ⟨tracePair, _, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨queryIter, _, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨foldedQuerySum, _, run⟩ := run
        simp only [Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.done.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at run
        exact run.1.2.symm
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

/-- Every accepted current generated relation-loop return carries exactly the
snapshot supplied to that loop. -/
theorem accepted_relation_loop_returns_supplied_snapshot
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
    (snapshot : Option Snapshot) (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option Snapshot) (traceOut : Trace)
    (success :
      v6_transcript.finish_onefold_relation_after_prechallenge_loop
        queryFoldInst traceInst iter transcript0 trace0 gamma runningClaim
        weights alpha foldedValues relationFields selector semanticPoint kappa
        queries compactCounter frontierNodes transcriptStateAfterQueries
        snapshot queryBatchChallenge authenticatedQueries =
          ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut)) :
    returnedSnapshot = snapshot := by
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop at success
  let body := tailBody queryFoldInst traceInst gamma relationFields selector
    semanticPoint kappa queries compactCounter frontierNodes
    transcriptStateAfterQueries snapshot queryBatchChallenge
    authenticatedQueries
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
  have loopRun : loop body
      (iter, transcript0, trace0, runningClaim, weights, alpha,
        foldedValues) =
      ok (core.result.Result.Ok (verified, returnedSnapshot), traceOut) := by
    rw [bodyEq] at success
    exact success
  obtain ⟨terminalState, terminalRun⟩ :=
    loop_ok_has_done_origin_eq body
      (iter, transcript0, trace0, runningClaim, weights, alpha, foldedValues)
      (core.result.Result.Ok (verified, returnedSnapshot), traceOut) loopRun
  exact tail_body_accepted_done_preserves_snapshot queryFoldInst traceInst
    gamma relationFields selector semanticPoint kappa queries compactCounter
    frontierNodes transcriptStateAfterQueries snapshot queryBatchChallenge
    authenticatedQueries terminalState verified returnedSnapshot traceOut
    terminalRun

/-- The exact shifted insertion and accepted relation-loop execution exposed
by the enclosing helper return the same snapshot option supplied before the
query-batch challenge. -/
theorem
    V7CallerCurrentReleaseR26AcceptedTailDispatch.AcceptedShiftedTailDispatch.returnedSnapshotExact
    {QueryFold Trace : Type}
    {queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError)}
    {traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit}
    {gamma : field.QM31}
    {relationFields : Array (Array field.QM31 6#usize) 4#usize}
    {selector : Std.U8} {semanticPoint : Array field.QM31 10#usize}
    {kappa : field.QM31} {queries : Array Std.U32 16#usize}
    {compactCounter : Std.U8} {frontierNodes : Std.Usize}
    {transcriptStateAfterQueries : Array Std.U8 32#usize}
    {snapshot : Option Snapshot} {alpha : Array field.QM31 4#usize}
    {foldedValues : Array field.QM31 256#usize}
    {weights : sumcheck.WeightAccumulator} {runningClaim : field.QM31}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option Snapshot} {traceOut : Trace}
    (dispatch :
      V7CallerCurrentReleaseR26AcceptedTailDispatch.AcceptedShiftedTailDispatch
        queryFoldInst traceInst gamma relationFields selector semanticPoint
        kappa queries compactCounter frontierNodes transcriptStateAfterQueries
        snapshot alpha foldedValues weights runningClaim verified
        returnedSnapshot traceOut) :
    returnedSnapshot = snapshot :=
  accepted_relation_loop_returns_supplied_snapshot queryFoldInst traceInst
    { start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS }
    dispatch.transcriptAfterClaim dispatch.traceAfterClaim gamma
    dispatch.runningClaimAfter dispatch.weightsAfter alpha foldedValues
    relationFields selector semanticPoint kappa queries compactCounter
    frontierNodes transcriptStateAfterQueries snapshot
    dispatch.queryBatchChallenge dispatch.authenticatedQueries verified
    returnedSnapshot traceOut dispatch.tailSuccess

#print axioms loop_ok_has_done_origin
#print axioms tail_body_accepted_done_preserves_snapshot
#print axioms accepted_relation_loop_returns_supplied_snapshot
#print axioms V7CallerCurrentReleaseR26AcceptedTailDispatch.AcceptedShiftedTailDispatch.returnedSnapshotExact

end V7CallerCurrentReleaseR26AcceptedTailSnapshot

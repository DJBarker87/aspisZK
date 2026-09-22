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

#print axioms loop_success_yields_exact_trace
#print axioms accepted_relation_loop_has_exact_trace

end V7CallerCurrentReleaseR26AcceptedTailTrace

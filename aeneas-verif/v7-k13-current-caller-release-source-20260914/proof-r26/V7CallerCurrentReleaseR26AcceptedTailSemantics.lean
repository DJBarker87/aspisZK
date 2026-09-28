import V7CallerCurrentReleaseR26AcceptedTailTrace

/-!
# Current R26 accepted-tail source semantics

This file inverts the four exact body equations retained by the accepted-loop
trace.  The first two rounds leave the accumulator unchanged; the third round
performs the current source's single `fold_tag73_relation_tail_arity4` call.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTailSemantics

abbrev TailState (Trace : Type) :=
  V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem qm31_ne_ok_false_iff_eq
    (left right : field.QM31) :
    core.cmp.PartialEq.ne.trait_default
        field.QM31.Insts.CoreCmpPartialEqQM31 left right = ok false ↔
      left = right := by
  rcases left with ⟨⟨left00, left01⟩, ⟨left10, left11⟩⟩
  rcases right with ⟨⟨right00, right01⟩, ⟨right10, right11⟩⟩
  by_cases h00 : left00 = right00 <;>
    by_cases h01 : left01 = right01 <;>
    by_cases h10 : left10 = right10 <;>
    by_cases h11 : left11 = right11 <;>
    simp [core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default,
      field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      field.M31.Insts.CoreCmpPartialEqM31.eq, h00, h01, h10, h11]

/-- Exact arithmetic and transcript facts exposed by the literal round-one
continuation edge.  The running-claim evaluation and value fold are retained
because they are the source data needed by the maintained candidate execution,
not merely control-flow witnesses. -/
structure RoundOneSourceStep
    {Trace : Type}
    (transcript0 : transcript.Transcript)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (after : TailState Trace) : Type where
  relationRow : Array field.QM31 6#usize
  polynomial : Array field.QM31 7#usize
  transcriptAbsorb : transcript.Transcript
  transcriptChallenge : transcript.Transcript
  alphaOne : field.QM31
  alphaAfter : Array field.QM31 4#usize
  alphaRead : field.QM31
  runningClaimAfter : field.QM31
  foldValuesAlpha : field.QM31
  foldedValuesAfter : Array field.QM31 256#usize
  relationRowSuccess : relationFields.index_usize 1#usize = ok relationRow
  polynomialSuccess :
    v6_transcript.decode_compact_relation_polynomial relationRow runningClaim =
      ok polynomial
  absorbSuccess :
    v6_transcript.absorb_compact_relation_polynomial transcript0 1#usize
      polynomial = ok transcriptAbsorb
  challengeSuccess : transcript.Transcript.impl.challenge_qm31
      transcriptAbsorb =
    ok (core.result.Result.Ok alphaOne, transcriptChallenge)
  alphaUpdateSuccess : alpha.update 1#usize alphaOne = ok alphaAfter
  alphaReadSuccess : alphaAfter.index_usize 1#usize = ok alphaRead
  evaluateSuccess : sumcheck.evaluate polynomial alphaRead =
    ok runningClaimAfter
  foldValuesAlphaSuccess : alphaAfter.index_usize 1#usize =
    ok foldValuesAlpha
  foldedValuesSuccess :
    v6_transcript.fold_values_prefix 256#usize foldedValues foldValuesAlpha =
      ok foldedValuesAfter
  transcriptAfterExact : after.2.1 = transcriptChallenge
  runningClaimAfterExact : after.2.2.2.1 = runningClaimAfter
  weightsUnchanged : after.2.2.2.2.1 = weights
  alphaAfterExact : after.2.2.2.2.2.1 = alphaAfter
  foldedValuesAfterExact : after.2.2.2.2.2.2 = foldedValuesAfter

/-- Inversion of the exact round-one body edge. -/
theorem round_one_edge_exposes_source_step
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
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (after : TailState Trace)
    (iterator :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS } :
            core.ops.range.Range Std.Usize) =
        ok (some 1#usize, after.1))
    (edge :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries
        ({ start := 1#usize, «end» := v6_onefold.V6_RELATION_ROUNDS },
          transcript0, trace0, runningClaim, weights, alpha, foldedValues) =
          ok (cont after)) :
    Nonempty (RoundOneSourceStep transcript0 runningClaim weights alpha
      foldedValues relationFields after) := by
  rcases after with
    ⟨iterAfter, transcriptAfter, traceAfter, runningClaimOut, weightsOut,
      alphaOut, foldedValuesOut⟩
  unfold V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody at edge
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at edge
  rw [iterator] at edge
  simp only [bind_tc_ok] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨relationRow, hrow, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨polynomial, hpoly, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨transcriptAbsorb, habsorb, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨challengePair, hchallenge, edge⟩ := edge
  rcases challengePair with ⟨challengeResult, transcriptChallenge⟩
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨mappedChallenge, hmap, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨flow, hbranch, edge⟩ := edge
  cases flow with
  | Break residual =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨residualResult, residualRun, edge⟩ := edge
      cases residual with
      | Ok impossible => cases impossible
      | Err error =>
          simp only [
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok,
            Aeneas.Std.Result.ok.injEq] at residualRun
          subst residualResult
          cases edge
  | Continue challenge =>
      cases challengeResult with
      | Err error =>
          simp only [core.result.Result.map_err] at hmap
          have mappedExact := Result.ok.inj hmap
          rw [← mappedExact] at hbranch
          simp [core.result.Result.Insts.CoreOpsTry.branch] at hbranch
      | Ok alphaOne =>
          simp only [core.result.Result.map_err] at hmap
          have mappedExact := Result.ok.inj hmap
          rw [← mappedExact] at hbranch
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            Aeneas.Std.Result.ok.injEq,
            core.ops.control_flow.ControlFlow.Continue.injEq] at hbranch
          rw [← hbranch] at edge
          simp only [UScalar.ofNatCore_val_eq] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨alphaAfter, halphaUpdate, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨alphaRead, halphaRead, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨runningClaimAfter, hevaluate, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨tracePolynomialPair, htracePolynomial, edge⟩ := edge
          rcases tracePolynomialPair with
            ⟨tracePolynomialUnit, tracePolynomial⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨lastRound, hlastRound, edge⟩ := edge
          have literalLast :
              lift (Std.Usize.wrapping_sub v6_onefold.V6_RELATION_ROUNDS
                1#usize) = (ok 3#usize : Result Std.Usize) := by
            simp only [v6_onefold.V6_RELATION_ROUNDS, lift]
            congr 1
            apply UScalar.eq_of_val_eq
            rw [Std.Usize.wrapping_sub_val_eq,
              UScalar.size_UScalarTyUsize]
            rcases System.Platform.numBits_eq with h | h <;>
              simp [Usize.size, Usize.numBits, h]
          have lastRoundExact : lastRound = 3#usize := by
            exact Result.ok.inj (hlastRound.symm.trans literalLast)
          subst lastRound
          have roundOneNotLast : (1#usize : Std.Usize) ≠ 3#usize := by
            norm_num
          simp only [roundOneNotLast, ↓reduceIte] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨traceWeightsPair, htraceWeights, edge⟩ := edge
          rcases traceWeightsPair with ⟨traceWeightsUnit, traceWeights⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨foldAlpha, hfoldAlpha, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨foldedValuesAfter, hfolded, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨traceRoundPair, htraceRound, edge⟩ := edge
          rcases traceRoundPair with ⟨traceRoundUnit, traceRound⟩
          simp only [Aeneas.Std.Result.ok.injEq,
            Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq] at edge
          rcases edge with
            ⟨iterExact, transcriptExact, traceExact, runningClaimExact,
              weightsExact, alphaExact, foldedValuesExact⟩
          exact ⟨{
            relationRow := relationRow
            polynomial := polynomial
            transcriptAbsorb := transcriptAbsorb
            transcriptChallenge := transcriptChallenge
            alphaOne := alphaOne
            alphaAfter := alphaAfter
            alphaRead := alphaRead
            runningClaimAfter := runningClaimAfter
            foldValuesAlpha := foldAlpha
            foldedValuesAfter := foldedValuesAfter
            relationRowSuccess := hrow
            polynomialSuccess := hpoly
            absorbSuccess := habsorb
            challengeSuccess := hchallenge
            alphaUpdateSuccess := halphaUpdate
            alphaReadSuccess := halphaRead
            evaluateSuccess := hevaluate
            foldValuesAlphaSuccess := hfoldAlpha
            foldedValuesSuccess := hfolded
            transcriptAfterExact := transcriptExact.symm
            runningClaimAfterExact := runningClaimExact.symm
            weightsUnchanged := weightsExact.symm
            alphaAfterExact := alphaExact.symm
            foldedValuesAfterExact := foldedValuesExact.symm }⟩

/-- Exact arithmetic and transcript facts exposed by the literal round-two
continuation edge. -/
structure RoundTwoSourceStep
    {Trace : Type}
    (transcript0 : transcript.Transcript)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (after : TailState Trace) : Type where
  relationRow : Array field.QM31 6#usize
  polynomial : Array field.QM31 7#usize
  transcriptAbsorb : transcript.Transcript
  transcriptChallenge : transcript.Transcript
  alphaTwo : field.QM31
  alphaAfter : Array field.QM31 4#usize
  alphaRead : field.QM31
  runningClaimAfter : field.QM31
  foldValuesAlpha : field.QM31
  foldedValuesAfter : Array field.QM31 256#usize
  relationRowSuccess : relationFields.index_usize 2#usize = ok relationRow
  polynomialSuccess :
    v6_transcript.decode_compact_relation_polynomial relationRow runningClaim =
      ok polynomial
  absorbSuccess :
    v6_transcript.absorb_compact_relation_polynomial transcript0 2#usize
      polynomial = ok transcriptAbsorb
  challengeSuccess : transcript.Transcript.impl.challenge_qm31
      transcriptAbsorb =
    ok (core.result.Result.Ok alphaTwo, transcriptChallenge)
  alphaUpdateSuccess : alpha.update 2#usize alphaTwo = ok alphaAfter
  alphaReadSuccess : alphaAfter.index_usize 2#usize = ok alphaRead
  evaluateSuccess : sumcheck.evaluate polynomial alphaRead =
    ok runningClaimAfter
  foldValuesAlphaSuccess : alphaAfter.index_usize 2#usize =
    ok foldValuesAlpha
  foldedValuesSuccess :
    v6_transcript.fold_values_prefix 64#usize foldedValues foldValuesAlpha =
      ok foldedValuesAfter
  transcriptAfterExact : after.2.1 = transcriptChallenge
  runningClaimAfterExact : after.2.2.2.1 = runningClaimAfter
  weightsUnchanged : after.2.2.2.2.1 = weights
  alphaAfterExact : after.2.2.2.2.2.1 = alphaAfter
  foldedValuesAfterExact : after.2.2.2.2.2.2 = foldedValuesAfter

/-- Inversion of the exact round-two body edge. -/
theorem round_two_edge_exposes_source_step
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
    (iter0 : core.ops.range.Range Std.Usize)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (after : TailState Trace)
    (iterator :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter0 =
        ok (some 2#usize, after.1))
    (edge :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries
        (iter0, transcript0, trace0, runningClaim, weights, alpha,
          foldedValues) = ok (cont after)) :
    Nonempty (RoundTwoSourceStep transcript0 runningClaim weights alpha
      foldedValues relationFields after) := by
  rcases after with
    ⟨iterAfter, transcriptAfter, traceAfter, runningClaimOut, weightsOut,
      alphaOut, foldedValuesOut⟩
  unfold V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody at edge
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at edge
  rw [iterator] at edge
  simp only [bind_tc_ok] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨relationRow, hrow, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨polynomial, hpoly, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨transcriptAbsorb, habsorb, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨challengePair, hchallenge, edge⟩ := edge
  rcases challengePair with ⟨challengeResult, transcriptChallenge⟩
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨mappedChallenge, hmap, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨flow, hbranch, edge⟩ := edge
  cases flow with
  | Break residual =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨residualResult, residualRun, edge⟩ := edge
      cases residual with
      | Ok impossible => cases impossible
      | Err error =>
          simp only [
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok,
            Aeneas.Std.Result.ok.injEq] at residualRun
          subst residualResult
          cases edge
  | Continue challenge =>
      cases challengeResult with
      | Err error =>
          simp only [core.result.Result.map_err] at hmap
          have mappedExact := Result.ok.inj hmap
          rw [← mappedExact] at hbranch
          simp [core.result.Result.Insts.CoreOpsTry.branch] at hbranch
      | Ok alphaTwo =>
          simp only [core.result.Result.map_err] at hmap
          have mappedExact := Result.ok.inj hmap
          rw [← mappedExact] at hbranch
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            Aeneas.Std.Result.ok.injEq,
            core.ops.control_flow.ControlFlow.Continue.injEq] at hbranch
          rw [← hbranch] at edge
          simp only [UScalar.ofNatCore_val_eq] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨alphaAfter, halphaUpdate, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨alphaRead, halphaRead, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨runningClaimAfter, hevaluate, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨tracePolynomialPair, htracePolynomial, edge⟩ := edge
          rcases tracePolynomialPair with
            ⟨tracePolynomialUnit, tracePolynomial⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨lastRound, hlastRound, edge⟩ := edge
          have literalLast :
              lift (Std.Usize.wrapping_sub v6_onefold.V6_RELATION_ROUNDS
                1#usize) = (ok 3#usize : Result Std.Usize) := by
            simp only [v6_onefold.V6_RELATION_ROUNDS, lift]
            congr 1
            apply UScalar.eq_of_val_eq
            rw [Std.Usize.wrapping_sub_val_eq,
              UScalar.size_UScalarTyUsize]
            rcases System.Platform.numBits_eq with h | h <;>
              simp [Usize.size, Usize.numBits, h]
          have lastRoundExact : lastRound = 3#usize := by
            exact Result.ok.inj (hlastRound.symm.trans literalLast)
          subst lastRound
          have roundTwoNotLast : (2#usize : Std.Usize) ≠ 3#usize := by
            norm_num
          simp only [roundTwoNotLast, ↓reduceIte] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨traceWeightsPair, htraceWeights, edge⟩ := edge
          rcases traceWeightsPair with ⟨traceWeightsUnit, traceWeights⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨foldAlpha, hfoldAlpha, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨foldedValuesAfter, hfolded, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨traceRoundPair, htraceRound, edge⟩ := edge
          rcases traceRoundPair with ⟨traceRoundUnit, traceRound⟩
          simp only [Aeneas.Std.Result.ok.injEq,
            Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq] at edge
          rcases edge with
            ⟨iterExact, transcriptExact, traceExact, runningClaimExact,
              weightsExact, alphaExact, foldedValuesExact⟩
          exact ⟨{
            relationRow := relationRow
            polynomial := polynomial
            transcriptAbsorb := transcriptAbsorb
            transcriptChallenge := transcriptChallenge
            alphaTwo := alphaTwo
            alphaAfter := alphaAfter
            alphaRead := alphaRead
            runningClaimAfter := runningClaimAfter
            foldValuesAlpha := foldAlpha
            foldedValuesAfter := foldedValuesAfter
            relationRowSuccess := hrow
            polynomialSuccess := hpoly
            absorbSuccess := habsorb
            challengeSuccess := hchallenge
            alphaUpdateSuccess := halphaUpdate
            alphaReadSuccess := halphaRead
            evaluateSuccess := hevaluate
            foldValuesAlphaSuccess := hfoldAlpha
            foldedValuesSuccess := hfolded
            transcriptAfterExact := transcriptExact.symm
            runningClaimAfterExact := runningClaimExact.symm
            weightsUnchanged := weightsExact.symm
            alphaAfterExact := alphaExact.symm
            foldedValuesAfterExact := foldedValuesExact.symm }⟩

/-- Exact facts exposed by the literal round-three edge, including the
current source's single optimized relation-tail weight fold. -/
structure RoundThreeSourceStep
    {Trace : Type}
    (transcript0 : transcript.Transcript)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (after : TailState Trace) : Type where
  relationRow : Array field.QM31 6#usize
  polynomial : Array field.QM31 7#usize
  transcriptAbsorb : transcript.Transcript
  transcriptChallenge : transcript.Transcript
  alphaThree : field.QM31
  alphaAfter : Array field.QM31 4#usize
  alphaRead : field.QM31
  runningClaimAfter : field.QM31
  q1 : field.QM31
  q2 : field.QM31
  q3 : field.QM31
  weightsAfter : sumcheck.WeightAccumulator
  foldValuesAlpha : field.QM31
  foldedValuesAfter : Array field.QM31 256#usize
  relationRowSuccess : relationFields.index_usize 3#usize = ok relationRow
  polynomialSuccess :
    v6_transcript.decode_compact_relation_polynomial relationRow runningClaim =
      ok polynomial
  absorbSuccess :
    v6_transcript.absorb_compact_relation_polynomial transcript0 3#usize
      polynomial = ok transcriptAbsorb
  challengeSuccess : transcript.Transcript.impl.challenge_qm31
      transcriptAbsorb =
    ok (core.result.Result.Ok alphaThree, transcriptChallenge)
  alphaUpdateSuccess : alpha.update 3#usize alphaThree = ok alphaAfter
  alphaReadSuccess : alphaAfter.index_usize 3#usize = ok alphaRead
  evaluateSuccess : sumcheck.evaluate polynomial alphaRead =
    ok runningClaimAfter
  q1Success : alphaAfter.index_usize 1#usize = ok q1
  q2Success : alphaAfter.index_usize 2#usize = ok q2
  q3Success : alphaAfter.index_usize 3#usize = ok q3
  weightsFoldSuccess :
    sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4 weights
      (Array.make 3#usize [q1, q2, q3]) = ok (true, weightsAfter)
  foldValuesAlphaSuccess : alphaAfter.index_usize 3#usize = ok foldValuesAlpha
  foldedValuesSuccess :
    v6_transcript.fold_values_prefix 16#usize foldedValues foldValuesAlpha =
      ok foldedValuesAfter
  transcriptAfterExact : after.2.1 = transcriptChallenge
  runningClaimAfterExact : after.2.2.2.1 = runningClaimAfter
  weightsAfterExact : after.2.2.2.2.1 = weightsAfter
  alphaAfterExact : after.2.2.2.2.2.1 = alphaAfter
  foldedValuesAfterExact : after.2.2.2.2.2.2 = foldedValuesAfter

/-- Inversion of the exact round-three body edge. -/
theorem round_three_edge_exposes_source_step
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
    (iter0 : core.ops.range.Range Std.Usize)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (after : TailState Trace)
    (iterator :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter0 =
        ok (some 3#usize, after.1))
    (edge :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries
        (iter0, transcript0, trace0, runningClaim, weights, alpha,
          foldedValues) = ok (cont after)) :
    Nonempty (RoundThreeSourceStep transcript0 runningClaim weights alpha
      foldedValues relationFields after) := by
  rcases after with
    ⟨iterAfter, transcriptAfter, traceAfter, runningClaimOut, weightsOut,
      alphaOut, foldedValuesOut⟩
  unfold V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody at edge
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at edge
  rw [iterator] at edge
  simp only [bind_tc_ok] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨relationRow, hrow, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨polynomial, hpoly, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨transcriptAbsorb, habsorb, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨challengePair, hchallenge, edge⟩ := edge
  rcases challengePair with ⟨challengeResult, transcriptChallenge⟩
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨mappedChallenge, hmap, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨flow, hbranch, edge⟩ := edge
  cases flow with
  | Break residual =>
      simp only at edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨residualResult, residualRun, edge⟩ := edge
      cases residual with
      | Ok impossible => cases impossible
      | Err error =>
          simp only [
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok,
            Aeneas.Std.Result.ok.injEq] at residualRun
          subst residualResult
          cases edge
  | Continue challenge =>
      cases challengeResult with
      | Err error =>
          simp only [core.result.Result.map_err] at hmap
          have mappedExact := Result.ok.inj hmap
          rw [← mappedExact] at hbranch
          simp [core.result.Result.Insts.CoreOpsTry.branch] at hbranch
      | Ok alphaThree =>
          simp only [core.result.Result.map_err] at hmap
          have mappedExact := Result.ok.inj hmap
          rw [← mappedExact] at hbranch
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            Aeneas.Std.Result.ok.injEq,
            core.ops.control_flow.ControlFlow.Continue.injEq] at hbranch
          rw [← hbranch] at edge
          simp only [UScalar.ofNatCore_val_eq] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨alphaAfter, halphaUpdate, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨alphaRead, halphaRead, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨runningClaimAfter, hevaluate, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨tracePolynomialPair, htracePolynomial, edge⟩ := edge
          rcases tracePolynomialPair with
            ⟨tracePolynomialUnit, tracePolynomial⟩
          rw [bind_eq_ok_iff] at edge
          obtain ⟨lastRound, hlastRound, edge⟩ := edge
          have literalLast :
              lift (Std.Usize.wrapping_sub v6_onefold.V6_RELATION_ROUNDS
                1#usize) = (ok 3#usize : Result Std.Usize) := by
            simp only [v6_onefold.V6_RELATION_ROUNDS, lift]
            congr 1
            apply UScalar.eq_of_val_eq
            rw [Std.Usize.wrapping_sub_val_eq,
              UScalar.size_UScalarTyUsize]
            rcases System.Platform.numBits_eq with h | h <;>
              simp [Usize.size, Usize.numBits, h]
          have lastRoundExact : lastRound = 3#usize := by
            exact Result.ok.inj (hlastRound.symm.trans literalLast)
          subst lastRound
          simp only [↓reduceIte] at edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨q1, hq1, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨q2, hq2, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨q3, hq3, edge⟩ := edge
          rw [bind_eq_ok_iff] at edge
          obtain ⟨foldPair, hweightsFold, edge⟩ := edge
          rcases foldPair with ⟨folded, weightsAfter⟩
          by_cases foldedTrue : folded = true
          · simp only [foldedTrue, ↓reduceIte] at edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨traceWeightsPair, htraceWeights, edge⟩ := edge
            rcases traceWeightsPair with ⟨traceWeightsUnit, traceWeights⟩
            rw [bind_eq_ok_iff] at edge
            obtain ⟨foldValuesAlpha, hfoldValuesAlpha, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨foldedValuesAfter, hfolded, edge⟩ := edge
            rw [bind_eq_ok_iff] at edge
            obtain ⟨traceRoundPair, htraceRound, edge⟩ := edge
            rcases traceRoundPair with ⟨traceRoundUnit, traceRound⟩
            simp only [Aeneas.Std.Result.ok.injEq,
              Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq] at edge
            rcases edge with
              ⟨iterExact, transcriptExact, traceExact, runningClaimExact,
                weightsExact, alphaExact, foldedValuesExact⟩
            subst folded
            exact ⟨{
              relationRow := relationRow
              polynomial := polynomial
              transcriptAbsorb := transcriptAbsorb
              transcriptChallenge := transcriptChallenge
              alphaThree := alphaThree
              alphaAfter := alphaAfter
              alphaRead := alphaRead
              runningClaimAfter := runningClaimAfter
              q1 := q1
              q2 := q2
              q3 := q3
              weightsAfter := weightsAfter
              foldValuesAlpha := foldValuesAlpha
              foldedValuesAfter := foldedValuesAfter
              relationRowSuccess := hrow
              polynomialSuccess := hpoly
              absorbSuccess := habsorb
              challengeSuccess := hchallenge
              alphaUpdateSuccess := halphaUpdate
              alphaReadSuccess := halphaRead
              evaluateSuccess := hevaluate
              q1Success := hq1
              q2Success := hq2
              q3Success := hq3
              weightsFoldSuccess := hweightsFold
              foldValuesAlphaSuccess := hfoldValuesAlpha
              foldedValuesSuccess := hfolded
              transcriptAfterExact := transcriptExact.symm
              runningClaimAfterExact := runningClaimExact.symm
              weightsAfterExact := weightsExact.symm
              alphaAfterExact := alphaExact.symm
              foldedValuesAfterExact := foldedValuesExact.symm }⟩
          · simp only [foldedTrue] at edge
            cases edge

/-- Exact facts exposed by the accepted terminal edge. -/
structure AcceptedTerminalSourceStep
    {Trace : Type}
    (gamma : field.QM31) (kappa : field.QM31)
    (selector : Std.U8) (semanticPoint : Array field.QM31 10#usize)
    (queries : Array Std.U32 16#usize)
    (compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (queryBatchChallenge : field.QM31)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace) : Type where
  terminalPrefix : Slice field.QM31
  terminalDot : field.QM31
  queryIterator : core.array.iter.IntoIter field.QM31 16#usize
  foldedQuerySum : field.QM31
  terminalPrefixSuccess :
    core.array.Array.index
        (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31))
        foldedValues { «end» := 4#usize } = ok terminalPrefix
  terminalDotSuccess :
    sumcheck.WeightAccumulator.impl.dot weights terminalPrefix = ok terminalDot
  terminalNeSuccess :
    core.cmp.PartialEq.ne.trait_default
        field.QM31.Insts.CoreCmpPartialEqQM31 terminalDot runningClaim =
      ok false
  terminalExact : terminalDot = runningClaim
  queryIteratorSuccess :
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      authenticatedQueries.values = ok queryIterator
  foldedQuerySumSuccess :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
        (BuiltinFnMut (field.QM31 × field.QM31) field.QM31) queryIterator
        field.QM31.ZERO (fun pair => field.QM31.add pair.1 pair.2) =
      ok foldedQuerySum
  outputExact : verified = {
    gamma
    kappa
    alpha
    queries
    selector
    compact_counter := compactCounter
    frontier_nodes := frontierNodes
    semantic_point := semanticPoint
    query_batch_challenge := queryBatchChallenge
    folded_query_sum := foldedQuerySum
    transcript_state_after_queries := transcriptStateAfterQueries
  }
  snapshotExact : returnedSnapshot = snapshot

/-- Inversion of the exact accepted terminal body edge. -/
theorem terminal_edge_exposes_source_step
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
    (iter0 terminalIterator : core.ops.range.Range Std.Usize)
    (transcript0 : transcript.Transcript) (trace0 : Trace)
    (runningClaim : field.QM31) (weights : sumcheck.WeightAccumulator)
    (alpha : Array field.QM31 4#usize)
    (foldedValues : Array field.QM31 256#usize)
    (verified : v6_transcript.V6VerifiedTranscript)
    (returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (traceOut : Trace)
    (iterator :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter0 =
        ok (none, terminalIterator))
    (edge :
      V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody queryFoldInst
        traceInst gamma relationFields selector semanticPoint kappa queries
        compactCounter frontierNodes transcriptStateAfterQueries snapshot
        queryBatchChallenge authenticatedQueries
        (iter0, transcript0, trace0, runningClaim, weights, alpha,
          foldedValues) =
        ok (done (core.result.Result.Ok (verified, returnedSnapshot),
          traceOut))) :
    Nonempty (AcceptedTerminalSourceStep gamma kappa selector semanticPoint
      queries compactCounter frontierNodes transcriptStateAfterQueries
      snapshot queryBatchChallenge authenticatedQueries runningClaim weights
      alpha foldedValues verified returnedSnapshot traceOut) := by
  unfold V7CallerCurrentReleaseR26AcceptedTailSnapshot.tailBody at edge
  unfold v6_transcript.finish_onefold_relation_after_prechallenge_loop.body at edge
  rw [iterator] at edge
  simp only [bind_tc_ok] at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨terminalPrefix, hprefix, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨terminalDot, hdot, edge⟩ := edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨terminalMismatch, hne, edge⟩ := edge
  by_cases mismatch : terminalMismatch = true
  · simp [mismatch] at edge
  · have mismatchFalse : terminalMismatch = false := Bool.eq_false_of_not_eq_true mismatch
    simp only [mismatchFalse, Bool.false_eq_true, ↓reduceIte] at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨tracePair, htrace, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨queryIterator, hqueryIterator, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨foldedQuerySum, hfoldedQuerySum, edge⟩ := edge
    have doneExact := Result.ok.inj edge
    have returnedPairExact := ControlFlow.done.inj doneExact
    have acceptedResultExact := congrArg Prod.fst returnedPairExact
    have acceptedPairExact := core.result.Result.Ok.inj acceptedResultExact
    have outputExact := congrArg Prod.fst acceptedPairExact
    have snapshotExact := congrArg Prod.snd acceptedPairExact
    have neFalse :
        core.cmp.PartialEq.ne.trait_default
            field.QM31.Insts.CoreCmpPartialEqQM31 terminalDot runningClaim =
          ok false := hne.trans (congrArg Result.ok mismatchFalse)
    exact ⟨{
      terminalPrefix := terminalPrefix
      terminalDot := terminalDot
      queryIterator := queryIterator
      foldedQuerySum := foldedQuerySum
      terminalPrefixSuccess := hprefix
      terminalDotSuccess := hdot
      terminalNeSuccess := neFalse
      terminalExact := (qm31_ne_ok_false_iff_eq terminalDot runningClaim).mp neFalse
      queryIteratorSuccess := hqueryIterator
      foldedQuerySumSuccess := hfoldedQuerySum
      outputExact := outputExact.symm
      snapshotExact := snapshotExact.symm }⟩

end V7CallerCurrentReleaseR26AcceptedTailSemantics

import V7CallerCurrentReleaseR26TerminalPrefixSemantics
import V7CallerCurrentReleaseR26AcceptedRelationWeightSemantics

/-!
# Accepted production terminal edge, end to end

This module joins the literal three-round source trace, the optimized
three-alpha weight fold, the four-value terminal slice, and the production
terminal dot.  The resulting equality is stated in the maintained K1 model.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26AcceptedTailComposition
open V7CallerCurrentReleaseR26AcceptedRelationRoundsSemantics
open V7CallerCurrentReleaseR26AcceptedRelationWeightSemantics
open V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics
open V7CallerCurrentReleaseR26AcceptedWeightVectorSemantics
open V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
open V7CallerCurrentReleaseR26TerminalPrefixSemantics
open V7CallerCurrentReleaseR26TerminalDotSource
open V7CallerCurrentReleaseR26TerminalStructuredComponents
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge
open V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26RelationDecodeSemantics
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def threeRoundWeightVector
    (alphaOne alphaTwo alphaThree : RawQM31)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (deferredAlpha : RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31) : Fin 4 → ModelQM31 :=
  dualWeightFoldLayer 4 (exactRaw alphaThree)
    (dualWeightFoldLayer 16 (exactRaw alphaTwo)
      (dualWeightFoldLayer 64 (exactRaw alphaOne)
        (inputWeightVector mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2
          deferredAlpha tScale0 tScale1 tFactors0 tFactors1 lineScales
          lineXs)))

def threeRoundValueVector
    (values : Array RawQM31 256#usize)
    (alphaOne alphaTwo alphaThree : RawQM31) : Fin 4 → ModelQM31 :=
  coefficientFoldLayer 4 (exactRaw alphaThree)
    (coefficientFoldLayer 16 (exactRaw alphaTwo)
      (coefficientFoldLayer 64 (exactRaw alphaOne)
        (modelPrefix values 256)))

theorem accepted_terminal_source_corresponds
    {Trace : Type}
    {gamma : RawQM31}
    {relationFields : Array (Array RawQM31 6#usize) 4#usize}
    {selector : Std.U8} {semanticPoint : Array RawQM31 10#usize}
    {kappa : RawQM31} {queries : Array Std.U32 16#usize}
    {compactCounter : Std.U8} {frontierNodes : Std.Usize}
    {transcriptStateAfterQueries : Array Std.U8 32#usize}
    {snapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {queryBatchChallenge : RawQM31}
    {authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch}
    {transcript0 : transcript.Transcript} {trace0 : Trace}
    {runningClaim : RawQM31} {weights : sumcheck.WeightAccumulator}
    {alpha : Array RawQM31 4#usize}
    {foldedValues : Array RawQM31 256#usize}
    {verified : v6_transcript.V6VerifiedTranscript}
    {returnedSnapshot : Option
      v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {traceOut : Trace}
    (source : AcceptedTailSourceTrace gamma relationFields selector
      semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries transcript0 trace0 runningClaim weights alpha
      foldedValues verified returnedSnapshot traceOut)
    (mScale0 mScale1 mScale2 : RawQM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31)
    (deferredAlpha : RawQM31)
    (groupValues : alloc.vec.Vec RawQM31)
    (tScale0 tScale1 : RawQM31)
    (tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (runningCanonical : GeneratedCanonicalQM31 runningClaim)
    (valuesCanonical : CanonicalValues foldedValues)
    (rowOneCanonical : CanonicalRelationRow source.roundOne.relationRow)
    (rowTwoCanonical : CanonicalRelationRow source.roundTwo.relationRow)
    (rowThreeCanonical : CanonicalRelationRow source.roundThree.relationRow)
    (alphaOneCanonical : GeneratedCanonicalQM31 source.roundOne.alphaOne)
    (alphaTwoCanonical : GeneratedCanonicalQM31 source.roundTwo.alphaTwo)
    (alphaThreeCanonical : GeneratedCanonicalQM31 source.roundThree.alphaThree)
    (inputComponents : weights.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
         (some deferredAlpha) groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs 0#u8])
    (deferredAlphaCanonical : GeneratedCanonicalQM31 deferredAlpha)
    (mScale0Canonical : GeneratedCanonicalQM31 mScale0)
    (mScale1Canonical : GeneratedCanonicalQM31 mScale1)
    (mScale2Canonical : GeneratedCanonicalQM31 mScale2)
    (mPoint0Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint0.val)
    (mPoint1Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint1.val)
    (mPoint2Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint2.val)
    (mPoint0Length : mPoint0.val.length = 8)
    (mPoint1Length : mPoint1.val.length = 8)
    (mPoint2Length : mPoint2.val.length = 8)
    (tScale0Canonical : GeneratedCanonicalQM31 tScale0)
    (tScale1Canonical : GeneratedCanonicalQM31 tScale1)
    (tFactors0Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList tFactors0.val)
    (tFactors1Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList tFactors1.val)
    (tFactors0Length : tFactors0.val.length = 8)
    (tFactors1Length : tFactors1.val.length = 8)
    (lineScalesLength : lineScales.val.length = 16)
    (lineXsLength : lineXs.val.length = 16)
    (lineScalesCanonical :
      CanonicalQM31Slice (alloc.vec.Vec.deref lineScales))
    (lineXsCanonical : CanonicalM31Slice (alloc.vec.Vec.deref lineXs)) :
    ∃ semantics : AcceptedWeightFoldSemantics source.afterTwo.2.2.2.2.1
        (Array.make 3#usize
          [source.roundThree.q1, source.roundThree.q2,
           source.roundThree.q3])
        source.roundThree.weightsAfter mScale0 mScale1 mScale2 mPoint0
        mPoint1 mPoint2 deferredAlpha groupValues tScale0 tScale1 tFactors0
        tFactors1 lineScales lineXs,
      GeneratedCanonicalQM31 source.roundThree.runningClaimAfter ∧
      sourceQm31ToModel
          (generatedQm31ToExact source.roundThree.runningClaimAfter) =
        candidateClaim (outputWeightVector semantics)
          (terminalValues source.terminal.terminalPrefix) ∧
      sourceQm31ToModel
          (generatedQm31ToExact source.roundThree.runningClaimAfter) =
        candidateClaim
          (threeRoundWeightVector source.roundOne.alphaOne
            source.roundTwo.alphaTwo source.roundThree.alphaThree mScale0
            mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha tScale0
            tScale1 tFactors0 tFactors1 lineScales lineXs)
          (threeRoundValueVector foldedValues source.roundOne.alphaOne
            source.roundTwo.alphaTwo source.roundThree.alphaThree) := by
  obtain ⟨rounds⟩ := accepted_relation_rounds_correspond source
    runningCanonical valuesCanonical rowOneCanonical rowTwoCanonical
    rowThreeCanonical alphaOneCanonical alphaTwoCanonical alphaThreeCanonical
  have q1Canonical : GeneratedCanonicalQM31 source.roundThree.q1 := by
    rw [rounds.q1Exact]
    exact alphaOneCanonical
  have q2Canonical : GeneratedCanonicalQM31 source.roundThree.q2 := by
    rw [rounds.q2Exact]
    exact alphaTwoCanonical
  have q3Canonical : GeneratedCanonicalQM31 source.roundThree.q3 := by
    rw [rounds.q3Exact]
    exact alphaThreeCanonical
  have inputComponentsAfter : source.afterTwo.2.2.2.2.1.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
         (some deferredAlpha) groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs 0#u8] := by
    rw [source.roundTwo.weightsUnchanged, source.roundOne.weightsUnchanged]
    exact inputComponents
  obtain ⟨semantics⟩ := accepted_relation_tail_weights_correspond source
    mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues
    tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs inputComponentsAfter
    deferredAlphaCanonical q1Canonical q2Canonical q3Canonical
    mScale0Canonical mScale1Canonical mScale2Canonical mPoint0Canonical
    mPoint1Canonical mPoint2Canonical mPoint0Length mPoint1Length
    mPoint2Length tScale0Canonical tScale1Canonical tFactors0Canonical
    tFactors1Canonical tFactors0Length tFactors1Length lineScalesLength
    lineXsLength lineScalesCanonical lineXsCanonical
  have terminalPrefixRun : core.array.Array.index
      (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice RawQM31))
      source.roundThree.foldedValuesAfter { «end» := 4#usize } =
        ok source.terminal.terminalPrefix := by
    rw [← source.roundThree.foldedValuesAfterExact]
    exact source.terminal.terminalPrefixSuccess
  obtain ⟨terminalLength, terminalCanonical, terminalValuesExact⟩ :=
    terminal_prefix_corresponds source.roundThree.foldedValuesAfter
      source.terminal.terminalPrefix rounds.valuesThreeCanonical
      terminalPrefixRun
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    accepted_terminal_dot_corresponds semantics source.terminal.terminalPrefix
      terminalCanonical terminalLength
  have terminalDotRun : sumcheck.WeightAccumulator.impl.dot
      source.roundThree.weightsAfter source.terminal.terminalPrefix =
        ok source.terminal.terminalDot := by
    rw [← source.roundThree.weightsAfterExact]
    exact source.terminal.terminalDotSuccess
  have outClaimExact : out = source.roundThree.runningClaimAfter :=
    (Result.ok.inj (outRun.symm.trans terminalDotRun)).trans
      (source.terminal.terminalExact.trans
        source.roundThree.runningClaimAfterExact)
  have claimExact : sourceQm31ToModel
        (generatedQm31ToExact source.roundThree.runningClaimAfter) =
      candidateClaim (outputWeightVector semantics)
        (terminalValues source.terminal.terminalPrefix) := by
    rw [← outClaimExact]
    exact outExact
  have alpha0Exact : semantics.trace.alpha0 = source.roundOne.alphaOne := by
    have read : semantics.trace.alpha0 = source.roundThree.q1 := by
      have run := semantics.trace.alpha0Read
      simpa [Array.index_usize] using (Result.ok.inj run).symm
    exact read.trans rounds.q1Exact
  have alpha1Exact : semantics.trace.alpha1 = source.roundTwo.alphaTwo := by
    have read : semantics.trace.alpha1 = source.roundThree.q2 := by
      have run := semantics.trace.alpha1Read
      simpa [Array.index_usize] using (Result.ok.inj run).symm
    exact read.trans rounds.q2Exact
  have alpha2Exact : semantics.trace.alpha2 = source.roundThree.alphaThree := by
    have read : semantics.trace.alpha2 = source.roundThree.q3 := by
      have run := semantics.trace.alpha2Read
      simpa [Array.index_usize] using (Result.ok.inj run).symm
    exact read.trans rounds.q3Exact
  let vector := accepted_weight_vector_corresponds semantics
  have finalWeightsExact :
      threeRoundWeightVector source.roundOne.alphaOne
          source.roundTwo.alphaTwo source.roundThree.alphaThree mScale0 mScale1
          mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha tScale0 tScale1
          tFactors0 tFactors1 lineScales lineXs =
        outputWeightVector semantics := by
    unfold threeRoundWeightVector
    simpa [alpha0Exact, alpha1Exact, alpha2Exact] using vector.finalWeightsExact
  have valuesOneExact : modelPrefix source.roundOne.foldedValuesAfter 64 =
      coefficientFoldLayer 64 (exactRaw source.roundOne.alphaOne)
        (modelPrefix foldedValues 256) := by
    funext fibre
    exact rounds.valuesOneExact fibre
  have valuesOneInputExact : modelPrefix source.afterOne.2.2.2.2.2.2 64 =
      coefficientFoldLayer 64 (exactRaw source.roundOne.alphaOne)
        (modelPrefix foldedValues 256) := by
    rw [source.roundOne.foldedValuesAfterExact]
    exact valuesOneExact
  have valuesTwoExact : modelPrefix source.roundTwo.foldedValuesAfter 16 =
      coefficientFoldLayer 16 (exactRaw source.roundTwo.alphaTwo)
        (coefficientFoldLayer 64 (exactRaw source.roundOne.alphaOne)
          (modelPrefix foldedValues 256)) := by
    funext fibre
    calc
      modelPrefix source.roundTwo.foldedValuesAfter 16 fibre =
          coefficientFoldLayer 16 (exactRaw source.roundTwo.alphaTwo)
            (modelPrefix source.afterOne.2.2.2.2.2.2 64) fibre :=
        rounds.valuesTwoExact fibre
      _ = coefficientFoldLayer 16 (exactRaw source.roundTwo.alphaTwo)
          (coefficientFoldLayer 64 (exactRaw source.roundOne.alphaOne)
            (modelPrefix foldedValues 256)) fibre := by
        rw [valuesOneInputExact]
  have valuesTwoInputExact : modelPrefix source.afterTwo.2.2.2.2.2.2 16 =
      coefficientFoldLayer 16 (exactRaw source.roundTwo.alphaTwo)
        (coefficientFoldLayer 64 (exactRaw source.roundOne.alphaOne)
          (modelPrefix foldedValues 256)) := by
    rw [source.roundTwo.foldedValuesAfterExact]
    exact valuesTwoExact
  have valuesThreeExact : modelPrefix source.roundThree.foldedValuesAfter 4 =
      threeRoundValueVector foldedValues source.roundOne.alphaOne
        source.roundTwo.alphaTwo source.roundThree.alphaThree := by
    funext fibre
    unfold threeRoundValueVector
    calc
      modelPrefix source.roundThree.foldedValuesAfter 4 fibre =
          coefficientFoldLayer 4 (exactRaw source.roundThree.alphaThree)
            (modelPrefix source.afterTwo.2.2.2.2.2.2 16) fibre :=
        rounds.valuesThreeExact fibre
      _ = coefficientFoldLayer 4 (exactRaw source.roundThree.alphaThree)
          (coefficientFoldLayer 16 (exactRaw source.roundTwo.alphaTwo)
            (coefficientFoldLayer 64 (exactRaw source.roundOne.alphaOne)
              (modelPrefix foldedValues 256))) fibre := by
        rw [valuesTwoInputExact]
  have finalValuesExact :
      terminalValues source.terminal.terminalPrefix =
        threeRoundValueVector foldedValues source.roundOne.alphaOne
          source.roundTwo.alphaTwo source.roundThree.alphaThree :=
    terminalValuesExact.trans valuesThreeExact
  have fullClaimExact : sourceQm31ToModel
        (generatedQm31ToExact source.roundThree.runningClaimAfter) =
      candidateClaim
        (threeRoundWeightVector source.roundOne.alphaOne
          source.roundTwo.alphaTwo source.roundThree.alphaThree mScale0 mScale1
          mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha tScale0 tScale1
          tFactors0 tFactors1 lineScales lineXs)
        (threeRoundValueVector foldedValues source.roundOne.alphaOne
          source.roundTwo.alphaTwo source.roundThree.alphaThree) := by
    calc
      _ = candidateClaim (outputWeightVector semantics)
          (terminalValues source.terminal.terminalPrefix) := claimExact
      _ = candidateClaim
          (threeRoundWeightVector source.roundOne.alphaOne
            source.roundTwo.alphaTwo source.roundThree.alphaThree mScale0
            mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha tScale0
            tScale1 tFactors0 tFactors1 lineScales lineXs)
          (terminalValues source.terminal.terminalPrefix) := by
        rw [finalWeightsExact]
      _ = candidateClaim
          (threeRoundWeightVector source.roundOne.alphaOne
            source.roundTwo.alphaTwo source.roundThree.alphaThree mScale0
            mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha tScale0
            tScale1 tFactors0 tFactors1 lineScales lineXs)
          (threeRoundValueVector foldedValues source.roundOne.alphaOne
            source.roundTwo.alphaTwo source.roundThree.alphaThree) := by
        rw [finalValuesExact]
  exact ⟨semantics, rounds.claimThreeCanonical, claimExact, fullClaimExact⟩

#print axioms accepted_terminal_source_corresponds

end V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd

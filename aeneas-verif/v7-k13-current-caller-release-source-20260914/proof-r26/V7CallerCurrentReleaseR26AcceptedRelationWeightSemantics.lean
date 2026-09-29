import V7CallerCurrentReleaseR26AcceptedTailComposition
import V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics

/-!
# Production relation-loop weight semantics

The round-three edge of an accepted generated relation loop contains the
public optimized weight-fold call.  This theorem instantiates its complete
source-to-K1 semantics with the three values read from the production alpha
array.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedRelationWeightSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailComposition
open V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31

theorem accepted_relation_tail_weights_correspond
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
    (inputComponents : source.afterTwo.2.2.2.2.1.components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Multilinear mScale2 mPoint2,
       .Grouped64x16BinaryDeferred releasedRowGroups64 releasedMasks
         (some deferredAlpha) groupValues,
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs 0#u8])
    (deferredAlphaCanonical : GeneratedCanonicalQM31 deferredAlpha)
    (q1Canonical : GeneratedCanonicalQM31 source.roundThree.q1)
    (q2Canonical : GeneratedCanonicalQM31 source.roundThree.q2)
    (q3Canonical : GeneratedCanonicalQM31 source.roundThree.q3)
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
    (lineScalesCanonical : CanonicalQM31Slice (alloc.vec.Vec.deref lineScales))
    (lineXsCanonical : CanonicalM31Slice (alloc.vec.Vec.deref lineXs)) :
    Nonempty (AcceptedWeightFoldSemantics source.afterTwo.2.2.2.2.1
      (Array.make 3#usize
        [source.roundThree.q1, source.roundThree.q2, source.roundThree.q3])
      source.roundThree.weightsAfter mScale0 mScale1 mScale2 mPoint0 mPoint1
      mPoint2 deferredAlpha groupValues tScale0 tScale1 tFactors0 tFactors1
      lineScales lineXs) := by
  have alpha0Canonical : ∀ trace : AcceptedTailWeightFoldTrace
      source.afterTwo.2.2.2.2.1
      (Array.make 3#usize
        [source.roundThree.q1, source.roundThree.q2, source.roundThree.q3])
      source.roundThree.weightsAfter,
      GeneratedCanonicalQM31 trace.alpha0 := by
    intro trace
    have exact : trace.alpha0 = source.roundThree.q1 := by
      have run := trace.alpha0Read
      simpa [Array.index_usize] using (Result.ok.inj run).symm
    rw [exact]
    exact q1Canonical
  have alpha1Canonical : ∀ trace : AcceptedTailWeightFoldTrace
      source.afterTwo.2.2.2.2.1
      (Array.make 3#usize
        [source.roundThree.q1, source.roundThree.q2, source.roundThree.q3])
      source.roundThree.weightsAfter,
      GeneratedCanonicalQM31 trace.alpha1 := by
    intro trace
    have exact : trace.alpha1 = source.roundThree.q2 := by
      have run := trace.alpha1Read
      simpa [Array.index_usize] using (Result.ok.inj run).symm
    rw [exact]
    exact q2Canonical
  have alpha2Canonical : ∀ trace : AcceptedTailWeightFoldTrace
      source.afterTwo.2.2.2.2.1
      (Array.make 3#usize
        [source.roundThree.q1, source.roundThree.q2, source.roundThree.q3])
      source.roundThree.weightsAfter,
      GeneratedCanonicalQM31 trace.alpha2 := by
    intro trace
    have exact : trace.alpha2 = source.roundThree.q3 := by
      have run := trace.alpha2Read
      simpa [Array.index_usize] using (Result.ok.inj run).symm
    rw [exact]
    exact q3Canonical
  exact accepted_weight_fold_corresponds source.afterTwo.2.2.2.2.1
    (Array.make 3#usize
      [source.roundThree.q1, source.roundThree.q2, source.roundThree.q3])
    source.roundThree.weightsAfter mScale0 mScale1 mScale2 mPoint0 mPoint1
    mPoint2 deferredAlpha groupValues tScale0 tScale1 tFactors0 tFactors1
    lineScales lineXs inputComponents deferredAlphaCanonical alpha0Canonical
    alpha1Canonical alpha2Canonical mScale0Canonical mScale1Canonical
    mScale2Canonical mPoint0Canonical mPoint1Canonical mPoint2Canonical
    mPoint0Length mPoint1Length mPoint2Length tScale0Canonical
    tScale1Canonical tFactors0Canonical tFactors1Canonical tFactors0Length
    tFactors1Length lineScalesLength lineXsLength lineScalesCanonical
    lineXsCanonical source.roundThree.weightsFoldSuccess

#print axioms accepted_relation_tail_weights_correspond

end V7CallerCurrentReleaseR26AcceptedRelationWeightSemantics

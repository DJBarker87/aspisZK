import V7CallerCurrentReleaseR26AcceptedTailArithmetic
import V7CallerCurrentReleaseR26AcceptedTailComposition
import V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge

/-!
# Accepted production relation-round semantics

One accepted generated relation loop carries three ordinary relation rounds
after the query insertion.  This module composes their exact claim updates and
their `256 -> 64 -> 16 -> 4` value-prefix folds in the maintained K1 field.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedRelationRoundsSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailSemantics
open V7CallerCurrentReleaseR26AcceptedTailComposition
open V7CallerCurrentReleaseR26AcceptedTailArithmetic
open V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
open V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26RelationDecodeSemantics
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness
open AspisV6TranscriptRelationGrammar

abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

private theorem update_one_reads_one
    (values updated : Array RawQM31 4#usize) (value : RawQM31)
    (run : values.update 1#usize value = ok updated) :
    updated.index_usize 1#usize = ok value := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_two_reads_two
    (values updated : Array RawQM31 4#usize) (value : RawQM31)
    (run : values.update 2#usize value = ok updated) :
    updated.index_usize 2#usize = ok value := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_two_preserves_one
    (values updated : Array RawQM31 4#usize) (value : RawQM31)
    (run : values.update 2#usize value = ok updated) :
    updated.index_usize 1#usize = values.index_usize 1#usize := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_three_reads_three
    (values updated : Array RawQM31 4#usize) (value : RawQM31)
    (run : values.update 3#usize value = ok updated) :
    updated.index_usize 3#usize = ok value := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_three_preserves_one
    (values updated : Array RawQM31 4#usize) (value : RawQM31)
    (run : values.update 3#usize value = ok updated) :
    updated.index_usize 1#usize = values.index_usize 1#usize := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_three_preserves_two
    (values updated : Array RawQM31 4#usize) (value : RawQM31)
    (run : values.update 3#usize value = ok updated) :
    updated.index_usize 2#usize = values.index_usize 2#usize := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

structure AcceptedRelationRoundsSemantics
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
    {returnedSnapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {traceOut : Trace}
    (source : AcceptedTailSourceTrace gamma relationFields selector
      semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries transcript0 trace0 runningClaim weights alpha
      foldedValues verified returnedSnapshot traceOut) : Type where
  q1Exact : source.roundThree.q1 = source.roundOne.alphaOne
  q2Exact : source.roundThree.q2 = source.roundTwo.alphaTwo
  q3Exact : source.roundThree.q3 = source.roundThree.alphaThree
  claimOneCanonical : GeneratedCanonicalQM31 source.roundOne.runningClaimAfter
  claimOneExact :
    sourceQm31ToModel
        (generatedQm31ToExact source.roundOne.runningClaimAfter) =
      relationEvaluate sourceQuarter
        (sourceQm31ToModel (generatedQm31ToExact runningClaim))
        (exactRelationParts source.roundOne.relationRow)
        (sourceQm31ToModel
          (generatedQm31ToExact source.roundOne.alphaOne))
  claimTwoCanonical : GeneratedCanonicalQM31 source.roundTwo.runningClaimAfter
  claimTwoExact :
    sourceQm31ToModel
        (generatedQm31ToExact source.roundTwo.runningClaimAfter) =
      relationEvaluate sourceQuarter
        (sourceQm31ToModel
          (generatedQm31ToExact source.afterOne.2.2.2.1))
        (exactRelationParts source.roundTwo.relationRow)
        (sourceQm31ToModel
          (generatedQm31ToExact source.roundTwo.alphaTwo))
  claimThreeCanonical :
    GeneratedCanonicalQM31 source.roundThree.runningClaimAfter
  claimThreeExact :
    sourceQm31ToModel
        (generatedQm31ToExact source.roundThree.runningClaimAfter) =
      relationEvaluate sourceQuarter
        (sourceQm31ToModel
          (generatedQm31ToExact source.afterTwo.2.2.2.1))
        (exactRelationParts source.roundThree.relationRow)
        (sourceQm31ToModel
          (generatedQm31ToExact source.roundThree.alphaThree))
  valuesOneCanonical : CanonicalValues source.roundOne.foldedValuesAfter
  valuesOneExact :
    ∀ fibre : Fin 64,
      sourceQm31ToModel
          (exactValueAt source.roundOne.foldedValuesAfter fibre.val) =
        coefficientFoldLayer 64
          (sourceQm31ToModel
            (generatedQm31ToExact source.roundOne.alphaOne))
          (modelPrefix foldedValues 256) fibre
  valuesTwoCanonical : CanonicalValues source.roundTwo.foldedValuesAfter
  valuesTwoExact :
    ∀ fibre : Fin 16,
      sourceQm31ToModel
          (exactValueAt source.roundTwo.foldedValuesAfter fibre.val) =
        coefficientFoldLayer 16
          (sourceQm31ToModel
            (generatedQm31ToExact source.roundTwo.alphaTwo))
          (modelPrefix source.afterOne.2.2.2.2.2.2 64) fibre
  valuesThreeCanonical : CanonicalValues source.roundThree.foldedValuesAfter
  valuesThreeExact :
    ∀ fibre : Fin 4,
      sourceQm31ToModel
          (exactValueAt source.roundThree.foldedValuesAfter fibre.val) =
        coefficientFoldLayer 4
          (sourceQm31ToModel
            (generatedQm31ToExact source.roundThree.alphaThree))
          (modelPrefix source.afterTwo.2.2.2.2.2.2 16) fibre

theorem accepted_relation_rounds_correspond
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
    {returnedSnapshot : Option v6_transcript.V6QueryBatchPrechallengeSnapshot}
    {traceOut : Trace}
    (source : AcceptedTailSourceTrace gamma relationFields selector
      semanticPoint kappa queries compactCounter frontierNodes
      transcriptStateAfterQueries snapshot queryBatchChallenge
      authenticatedQueries transcript0 trace0 runningClaim weights alpha
      foldedValues verified returnedSnapshot traceOut)
    (runningCanonical : GeneratedCanonicalQM31 runningClaim)
    (valuesCanonical : CanonicalValues foldedValues)
    (rowOneCanonical : CanonicalRelationRow source.roundOne.relationRow)
    (rowTwoCanonical : CanonicalRelationRow source.roundTwo.relationRow)
    (rowThreeCanonical : CanonicalRelationRow source.roundThree.relationRow)
    (alphaOneCanonical : GeneratedCanonicalQM31 source.roundOne.alphaOne)
    (alphaTwoCanonical : GeneratedCanonicalQM31 source.roundTwo.alphaTwo)
    (alphaThreeCanonical : GeneratedCanonicalQM31 source.roundThree.alphaThree) :
    Nonempty (AcceptedRelationRoundsSemantics source) := by
  have foldAlphaOneExact :
      source.roundOne.foldValuesAlpha = source.roundOne.alphaOne := by
    exact Result.ok.inj (source.roundOne.foldValuesAlphaSuccess.symm.trans
      (update_one_reads_one _ _ _ source.roundOne.alphaUpdateSuccess))
  have claimOne :=
    V7CallerCurrentReleaseR26AcceptedTailArithmetic.RoundOneSourceStep.runningClaimAfter_model_exact
      source.roundOne rowOneCanonical runningCanonical alphaOneCanonical
  obtain ⟨valuesOneCanonical, valuesOneExact⟩ :=
    fold_values_prefix_256_equals_model_layer foldedValues
      source.roundOne.foldedValuesAfter source.roundOne.foldValuesAlpha
      valuesCanonical (by simpa [foldAlphaOneExact] using alphaOneCanonical)
      source.roundOne.foldedValuesSuccess
  have claimOneInputCanonical :
      GeneratedCanonicalQM31 source.afterOne.2.2.2.1 := by
    rw [source.roundOne.runningClaimAfterExact]
    exact claimOne.1
  have valuesOneInputCanonical :
      CanonicalValues source.afterOne.2.2.2.2.2.2 := by
    rw [source.roundOne.foldedValuesAfterExact]
    exact valuesOneCanonical
  have foldAlphaTwoExact :
      source.roundTwo.foldValuesAlpha = source.roundTwo.alphaTwo := by
    exact Result.ok.inj (source.roundTwo.foldValuesAlphaSuccess.symm.trans
      (update_two_reads_two _ _ _ source.roundTwo.alphaUpdateSuccess))
  have claimTwo :=
    V7CallerCurrentReleaseR26AcceptedTailArithmetic.RoundTwoSourceStep.runningClaimAfter_model_exact
      source.roundTwo rowTwoCanonical claimOneInputCanonical alphaTwoCanonical
  obtain ⟨valuesTwoCanonical, valuesTwoExact⟩ :=
    fold_values_prefix_64_equals_model_layer
      source.afterOne.2.2.2.2.2.2 source.roundTwo.foldedValuesAfter
      source.roundTwo.foldValuesAlpha valuesOneInputCanonical
      (by simpa [foldAlphaTwoExact] using alphaTwoCanonical)
      source.roundTwo.foldedValuesSuccess
  have claimTwoInputCanonical :
      GeneratedCanonicalQM31 source.afterTwo.2.2.2.1 := by
    rw [source.roundTwo.runningClaimAfterExact]
    exact claimTwo.1
  have valuesTwoInputCanonical :
      CanonicalValues source.afterTwo.2.2.2.2.2.2 := by
    rw [source.roundTwo.foldedValuesAfterExact]
    exact valuesTwoCanonical
  have foldAlphaThreeExact :
      source.roundThree.foldValuesAlpha = source.roundThree.alphaThree := by
    exact Result.ok.inj (source.roundThree.foldValuesAlphaSuccess.symm.trans
      (update_three_reads_three _ _ _ source.roundThree.alphaUpdateSuccess))
  have claimThree :=
    V7CallerCurrentReleaseR26AcceptedTailArithmetic.RoundThreeSourceStep.runningClaimAfter_model_exact
      source.roundThree rowThreeCanonical claimTwoInputCanonical
      alphaThreeCanonical
  obtain ⟨valuesThreeCanonical, valuesThreeExact⟩ :=
    fold_values_prefix_16_equals_model_layer
      source.afterTwo.2.2.2.2.2.2 source.roundThree.foldedValuesAfter
      source.roundThree.foldValuesAlpha valuesTwoInputCanonical
      (by simpa [foldAlphaThreeExact] using alphaThreeCanonical)
      source.roundThree.foldedValuesSuccess
  have q1Exact : source.roundThree.q1 = source.roundOne.alphaOne := by
    apply Result.ok.inj
    calc
      ok source.roundThree.q1 =
          source.roundThree.alphaAfter.index_usize 1#usize :=
        source.roundThree.q1Success.symm
      _ = source.afterTwo.2.2.2.2.2.1.index_usize 1#usize :=
        update_three_preserves_one _ _ _
          source.roundThree.alphaUpdateSuccess
      _ = source.roundTwo.alphaAfter.index_usize 1#usize :=
        congrArg (fun values => values.index_usize 1#usize)
          source.roundTwo.alphaAfterExact
      _ = source.afterOne.2.2.2.2.2.1.index_usize 1#usize :=
        update_two_preserves_one _ _ _ source.roundTwo.alphaUpdateSuccess
      _ = source.roundOne.alphaAfter.index_usize 1#usize :=
        congrArg (fun values => values.index_usize 1#usize)
          source.roundOne.alphaAfterExact
      _ = ok source.roundOne.alphaOne :=
        update_one_reads_one _ _ _ source.roundOne.alphaUpdateSuccess
  have q2Exact : source.roundThree.q2 = source.roundTwo.alphaTwo := by
    apply Result.ok.inj
    calc
      ok source.roundThree.q2 =
          source.roundThree.alphaAfter.index_usize 2#usize :=
        source.roundThree.q2Success.symm
      _ = source.afterTwo.2.2.2.2.2.1.index_usize 2#usize :=
        update_three_preserves_two _ _ _
          source.roundThree.alphaUpdateSuccess
      _ = source.roundTwo.alphaAfter.index_usize 2#usize :=
        congrArg (fun values => values.index_usize 2#usize)
          source.roundTwo.alphaAfterExact
      _ = ok source.roundTwo.alphaTwo :=
        update_two_reads_two _ _ _ source.roundTwo.alphaUpdateSuccess
  have q3Exact : source.roundThree.q3 = source.roundThree.alphaThree := by
    exact Result.ok.inj (source.roundThree.q3Success.symm.trans
      (update_three_reads_three _ _ _ source.roundThree.alphaUpdateSuccess))
  exact ⟨{
    q1Exact := q1Exact
    q2Exact := q2Exact
    q3Exact := q3Exact
    claimOneCanonical := claimOne.1
    claimOneExact := claimOne.2
    claimTwoCanonical := claimTwo.1
    claimTwoExact := claimTwo.2
    claimThreeCanonical := claimThree.1
    claimThreeExact := claimThree.2
    valuesOneCanonical := valuesOneCanonical
    valuesOneExact := by simpa [foldAlphaOneExact] using valuesOneExact
    valuesTwoCanonical := valuesTwoCanonical
    valuesTwoExact := by simpa [foldAlphaTwoExact] using valuesTwoExact
    valuesThreeCanonical := valuesThreeCanonical
    valuesThreeExact := by simpa [foldAlphaThreeExact] using valuesThreeExact }⟩

#print axioms accepted_relation_rounds_correspond

end V7CallerCurrentReleaseR26AcceptedRelationRoundsSemantics

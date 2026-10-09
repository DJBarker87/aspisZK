import FSV8AlignedAlphaChallengeRun
import FSV8AlphaCompleteCoordinateRouter
import FSV8AlphaTotalSuccessfulCoordinates
import FSV7FourBlockWordBridge
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting
import AspisFormal.K1.V7Tag73IncrementalSamplerControl

/-!
# Deterministic aligned alpha run to the complete routed tape

This leaf pads the one-to-four output/advance pairs of an actual
`SuccessfulAlignedChallenge` to the four-pair tape exposed by
`alpha0SamplerCoordinates`.  It proves that the padded output window has the
same successful ordinary decode and that every advance answer actually used
by the run is retained at the corresponding prefix coordinate.

Padding describes unused analysis coordinates only.  No freshness,
independence, cache, or probability premise occurs here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlignedAlphaTotalTape

open FSBoundedTranscript
open FSV8AlignedAlphaChallengeRun FSV8AlignedAlphaSqueezeStep
open FSV8CandidateOriginTrace
open FSV8AlphaTotalSuccessfulCoordinates
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73EightRetryDecoderBridge
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

def zeroBlock : Block := fun _ => 0

/-- Pad a chronological list to the four analysis coordinates.  The source
run itself never reads these padding values. -/
def padFour (blocks : List Block) : Fin 4 → Block :=
  fun index => blocks.getD index.val zeroBlock

theorem take_ofFn_padFour (blocks : List Block) (cap : blocks.length ≤ 4) :
    (List.ofFn (padFour blocks)).take blocks.length = blocks := by
  apply List.ext_getElem
  · simp [cap]
  · intro index leftBound rightBound
    simp only [List.getElem_take, List.getElem_ofFn]
    unfold padFour
    rw [List.getD_eq_getElem _ _ (by simpa using rightBound)]

/-- Chronological advance answers carried by a rejected aligned path.  This is
a proposition because `AlignedRejectedPath` itself is a proof object; it does
not use choice to manufacture execution data. -/
inductive AdvanceTrace
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} → {v7 : OracleState} → {s : Transcript} →
      AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s →
        List Block → Prop where
  | base (aligned) (prefixPath) :
      AdvanceTrace (@AlignedRejectedPath.base steps tape finiteTape limits
        startV7 start aligned prefixPath) []
  | snoc {prior v7 s} {path} {pair} {bounded} {reject} {advances}
      (priorTrace : AdvanceTrace path advances) :
      AdvanceTrace
        (@AlignedRejectedPath.snoc steps tape finiteTape limits startV7 start
          prior v7 s path pair bounded reject)
        (advances ++ [(advanceStep tape s).1])

theorem AdvanceTrace.length_eq
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    {path : AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s}
    {advances : List Block} (trace : AdvanceTrace path advances) :
    advances.length = blocks.length := by
  induction trace with
  | base => rfl
  | snoc priorTrace ih => simp [ih]

theorem AlignedRejectedPath.exists_advanceTrace
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    (path : AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s) :
    ∃ advances, AdvanceTrace path advances := by
  induction path with
  | base aligned prefixPath => exact ⟨[], .base aligned prefixPath⟩
  | @snoc prior v7 s path pair bounded reject ih =>
      obtain ⟨advances, trace⟩ := ih
      exact ⟨advances ++ [(advanceStep tape s).1],
        .snoc (bounded := bounded) (reject := reject) trace⟩

theorem successful_blocks_cap
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) : blocks.length ≤ 4 := by
  obtain ⟨rejected, finalStart, beforeFinal, rejectedPath, finalPair,
      blocksEq, finalEq, accepted, phase⟩ := success
  have ordinaryExact : decodeOrdinaryExact blocks = some value := by
    rw [blocksEq]
    simpa [decodeChallengeParameter, samplerMode] using accepted
  exact decodeOrdinaryExact_block_cap blocks value ordinaryExact

/-- Any complete routed tape whose output side has the consumed source prefix
of a successful aligned run succeeds and decodes to the same alpha.  The
advance side is deliberately unconstrained: it affects the causal source
history, but not the deterministic ordinary decoder.

This is the consumer interface needed by a source router.  It requires only
equality of the actually consumed output prefix; it does not require the
router's unused suffix to equal `padFour`, and it has no freshness or
probability premise. -/
theorem successfulTotalTape_of_output_prefix
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value)
    (total : RelationAlphaTotalTape)
    (outputPrefix : (List.ofFn total.1).take blocks.length = blocks) :
    ∃ decoded : OrdinaryPrefixDecode,
      decodeOrdinaryPrefix (List.ofFn total.1) = some decoded ∧
      decoded.value = value ∧ relationAlphaTotalSucceeds total := by
  have blocksCap := successful_blocks_cap success
  obtain ⟨_rejected, _finalStart, _beforeFinal, _rejectedPath, _finalPair,
      blocksEq, _finalEq, accepted, _phase⟩ := success
  have ordinaryExact : decodeOrdinaryExact blocks = some value := by
    rw [blocksEq]
    simpa [decodeChallengeParameter, samplerMode] using accepted
  obtain ⟨decoded, decodedAtBlocks, noRemaining, valueEq⟩ :=
    decodeOrdinaryExact_witness blocks value ordinaryExact
  have usedEq : decoded.blocksUsed = blocks.length := by
    have remaining := decodeOrdinaryPrefix_remaining_eq_drop
      blocks decoded decodedAtBlocks
    obtain ⟨_before, _acceptedWord, _after, _decomposition, _wordsUsed,
        _limbCount, _finalLimb, _value, _blocksUsed, _remaining,
        usedLe⟩ := decodeOrdinaryPrefix_fourth_limb_trace
          blocks decoded decodedAtBlocks
    have dropEmpty : blocks.drop decoded.blocksUsed = [] := by
      rw [← remaining]
      exact noRemaining
    have lengthLe := List.drop_eq_nil_iff.mp dropEmpty
    omega
  let routedBlocks := List.ofFn total.1
  have routedLong : decoded.blocksUsed ≤ routedBlocks.length := by
    rw [usedEq]
    simpa [routedBlocks] using blocksCap
  have prefixEq : routedBlocks.take decoded.blocksUsed =
      blocks.take decoded.blocksUsed := by
    rw [usedEq, outputPrefix]
    simp
  have routedRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
    blocks routedBlocks decoded decodedAtBlocks routedLong prefixEq
  refine ⟨{ decoded with
      remainingBlocks := routedBlocks.drop decoded.blocksUsed },
    routedRun, valueEq, ?_⟩
  unfold relationAlphaTotalSucceeds
  rw [← fourGammaBlocksRawEquiv_success_iff]
  rw [routedRun]
  rfl

/-- Padding the output side of an actual successful aligned run preserves its
returned alpha.  The result uses the same four-block/raw-stream bridge as the
complete coordinate router. -/
theorem successfulTotalTape_decodes_same_alpha
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ (total : RelationAlphaTotalTape) (advances : List Block)
      (decoded : OrdinaryPrefixDecode),
      total.1 = padFour blocks ∧
      (List.ofFn total.1).take blocks.length = blocks ∧
      advances.length = blocks.length ∧
      (List.ofFn total.2).take blocks.length = advances ∧
      FSV7FourBlockWordBridge.Current.fourBlockWords total.1 =
        (rawWordsToNat (fourGammaBlocksRawEquiv total.1).1).map maskedM31 ∧
      decodeOrdinaryPrefix (List.ofFn total.1) =
        some decoded ∧ decoded.value = value ∧
      Tag73RawSucceeds
        (fourGammaBlocksRawEquiv total.1) := by
  have blocksCap := successful_blocks_cap success
  obtain ⟨rejected, finalStart, beforeFinal, rejectedPath, finalPair,
      blocksEq, finalEq, accepted, phase⟩ := success
  obtain ⟨priorAdvances, priorTrace⟩ :=
    AlignedRejectedPath.exists_advanceTrace rejectedPath
  let advances := priorAdvances ++ [(advanceStep tape finalStart).1]
  have advancesLength : advances.length = blocks.length := by
    rw [blocksEq]
    simp [advances, priorTrace.length_eq]
  let total : RelationAlphaTotalTape := (padFour blocks, padFour advances)
  have outputPrefix : (List.ofFn total.1).take blocks.length = blocks := by
    exact take_ofFn_padFour blocks blocksCap
  have advancePrefix : (List.ofFn total.2).take blocks.length = advances := by
    change (List.ofFn (padFour advances)).take blocks.length = advances
    rw [← advancesLength]
    exact take_ofFn_padFour advances (by
      rw [advancesLength]
      exact blocksCap)
  have ordinaryExact : decodeOrdinaryExact blocks = some value := by
    rw [blocksEq]
    simpa [decodeChallengeParameter, samplerMode] using accepted
  obtain ⟨decoded, decodedAtBlocks, noRemaining, valueEq⟩ :=
    decodeOrdinaryExact_witness blocks value ordinaryExact
  have usedEq : decoded.blocksUsed = blocks.length := by
    have remaining := decodeOrdinaryPrefix_remaining_eq_drop
      blocks decoded decodedAtBlocks
    obtain ⟨_before, _acceptedWord, _after, _decomposition, _wordsUsed,
        _limbCount, _finalLimb, _value, _blocksUsed, _remaining,
        usedLe⟩ := decodeOrdinaryPrefix_fourth_limb_trace
          blocks decoded decodedAtBlocks
    have dropEmpty : blocks.drop decoded.blocksUsed = [] := by
      rw [← remaining]
      exact noRemaining
    have lengthLe := List.drop_eq_nil_iff.mp dropEmpty
    omega
  let routedBlocks := List.ofFn total.1
  have routedLong : decoded.blocksUsed ≤ routedBlocks.length := by
    rw [usedEq]
    simpa [routedBlocks] using blocksCap
  have prefixEq : routedBlocks.take decoded.blocksUsed =
      blocks.take decoded.blocksUsed := by
    rw [usedEq]
    rw [outputPrefix]
    simp
  have routedRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
    blocks routedBlocks decoded decodedAtBlocks routedLong prefixEq
  have rawSuccess : Tag73RawSucceeds
      (fourGammaBlocksRawEquiv total.1) := by
    rw [← fourGammaBlocksRawEquiv_success_iff]
    rw [routedRun]
    rfl
  have wordBridge : FSV7FourBlockWordBridge.Current.fourBlockWords total.1 =
      (rawWordsToNat (fourGammaBlocksRawEquiv total.1).1).map maskedM31 :=
    FSV7FourBlockWordBridge.current_fourBlockWords_eq_masked_fourGammaBlocksRawEquiv
      total.1
  refine ⟨total, advances,
    { decoded with remainingBlocks := routedBlocks.drop decoded.blocksUsed },
    rfl, outputPrefix, advancesLength, advancePrefix, wordBridge, routedRun,
    ?_, rawSuccess⟩
  exact valueEq

#print axioms take_ofFn_padFour
#print axioms AdvanceTrace.length_eq
#print axioms AlignedRejectedPath.exists_advanceTrace
#print axioms successful_blocks_cap
#print axioms successfulTotalTape_of_output_prefix
#print axioms successfulTotalTape_decodes_same_alpha

end
end AspisV8Completion.FSV8AlignedAlphaTotalTape

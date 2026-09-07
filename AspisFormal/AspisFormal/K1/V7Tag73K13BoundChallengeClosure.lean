import AspisFormal.K1.V7Tag73K13CorrectedPairProfileInvariant
import AspisFormal.K1.V7Tag73ExactAlphaZeroPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactAlphaZeroActualTrialPrefinal
import AspisFormal.K1.V7Tag73ExactRootCausalChain
import AspisFormal.K1.V7Tag73RawChallengeBinding

/-!
# K1.3 closure from explicit decoded-challenge bindings

Revision 2 absorbs the canonical decoded gamma and alpha-zero values.  This
file uses those literal absorptions as the causal boundary.  It never assigns
a logical role to an adversary-created raw squeeze coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13BoundChallengeClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroActualTrialPrefinal
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CorrectedPairProfileInvariant
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73K13PreQ16RootInvariant
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RawChallengeBinding
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

theorem gamma_to_alpha_bind_events_are_post_c1 (messages : Messages) :
    ∀ event,
      event ∈
          (afterGammaBindBeforeAlphaZeroTailEvents messages ++
            [challengeBindEvent messages .alphaZero]) →
        IsPostRootMachineEvent c1RootLabel event := by
  simp [afterGammaBindBeforeAlphaZeroTailEvents, oodEvents,
    IsPostRootMachineEvent, challengeEvent, challengeBindEvent,
    AspisK1.V7Tag73TranscriptSchedule.Payload.label, c1RootLabel,
    inactiveClaimLabel, circleOodValueLabel, relationRoundLabel,
    foldWorkNonceLabel, challengeBindLabel]

theorem gamma_middle_events_are_post_challenge_bind (messages : Messages) :
    ∀ event,
      event ∈ afterGammaBindBeforeAlphaZeroTailEvents messages →
        IsPostRootMachineEvent challengeBindLabel event := by
  simp [afterGammaBindBeforeAlphaZeroTailEvents, oodEvents,
    IsPostRootMachineEvent, challengeEvent,
    AspisK1.V7Tag73TranscriptSchedule.Payload.label,
    inactiveClaimLabel, circleOodValueLabel, relationRoundLabel,
    foldWorkNonceLabel, challengeBindLabel]

/-- The canonical final256 producer is literally shared by a clean pair. -/
theorem exact_preQ16_clean_pair_common_final256_record_v2
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    ∃ (leftBefore rightBefore : EvalState) (digest : Digest256)
        (leftActor rightActor : QueryActor),
      let leftInput := bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape leftWitness.joint.input).messages.finalValues
      let rightInput := bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape rightWitness.joint.input).messages.finalValues
      leftInput = rightInput ∧
        tableLookup (exactOperationalTable leftWitness.joint.input) leftInput =
          some digest ∧
        tableLookup (exactOperationalTable rightWitness.joint.input) rightInput =
          some digest ∧
        (.machineFresh leftActor leftInput digest : UnifiedExposureRecord) ∈
          leftWitness.joint.prior ∧
        (.machineFresh rightActor rightInput digest : UnifiedExposureRecord) ∈
          rightWitness.joint.prior ∧
        HasLiteralStatePrefix digest leftWitness.joint.pivotInput ∧
        HasLiteralStatePrefix digest rightWitness.joint.pivotInput := by
  classical
  obtain ⟨leftBefore, leftDigest, leftActor, leftLookup, leftMember,
      leftPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial leftWitness.joint
  obtain ⟨rightBefore, rightDigest, rightActor, rightLookup, rightMember,
      rightPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial rightWitness.joint
  have selectedInputExact := exact_preQ16_clean_pair_selected_input_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness priorExact
  have digestExact : leftDigest = rightDigest :=
    literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
      selectedInputExact
  let leftInput : ShaInput := bytes leftBefore.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape leftWitness.joint.input).messages.finalValues
  let rightInput : ShaInput := bytes rightBefore.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape rightWitness.joint.input).messages.finalValues
  have rightMemberCommon :
      (.machineFresh rightActor rightInput leftDigest : UnifiedExposureRecord) ∈
        leftWitness.joint.prior := by
    rw [priorExact]
    simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftWitness.joint.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have inputExact : leftInput = rightInput := by
    have recordExact :
        (.machineFresh leftActor leftInput leftDigest : UnifiedExposureRecord) =
          .machineFresh rightActor rightInput leftDigest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftInput,
          AspisK1.V7Tag73TranscriptSchedule.Payload.label,
          AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember)
        rightMemberCommon rfl
    injection recordExact
  refine ⟨leftBefore, rightBefore, leftDigest, leftActor, rightActor, ?_⟩
  exact ⟨inputExact,
    by simpa [leftInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftLookup,
    by simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightLookup,
    by simpa [leftInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember,
    by simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember,
    leftPrefix, by simpa [digestExact] using rightPrefix⟩

/-- Witness-neutral alpha-binding chronology.  The proof needs only the
literal selected-trial decomposition and the retained canonical `final256`
record.  In particular, it does not inspect the K1.3 bad set or the word from
which that set was derived.  This is the reusable source lemma required by
both the corrected pre-q16 classifier and restoration-wide extraction. -/
theorem exact_actual_alpha_binding_record_mem_prior
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (actualTrial : ExactFixedK13ActualJointTrial input finalTrial)
    (prior later : List UnifiedExposureRecord)
    (pivotActor : QueryActor) (pivotInput : ShaInput) (pivotAnswer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later)
    (trialExact : finalTrial.val = prior.length)
    (canonicalBefore : EvalState) (canonicalDigest : Digest256)
    (canonicalActor : QueryActor)
    (canonicalLookup : tableLookup (exactOperationalTable input)
      (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks (exactOperationalTape input).messages.finalValues) =
      some canonicalDigest)
    (canonicalMember :
      (.machineFresh canonicalActor
        (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks (exactOperationalTape input).messages.finalValues)
        canonicalDigest : UnifiedExposureRecord) ∈ prior)
    (canonicalPrefix : HasLiteralStatePrefix canonicalDigest pivotInput) :
    ∃ (afterSample : EvalState) (raw : Qm31Bytes) (value : QM31Exact)
        (actor : QueryActor),
      tableLookup (exactOperationalTable input)
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
              raw).data) = some canonicalBefore.digest ∧
      (.machineFresh actor
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
              raw).data) canonicalBefore.digest : UnifiedExposureRecord) ∈
        prior ∧
      raw = (exactOperationalTape input).messages.challengeValue (.alpha 0) ∧
      decodeTagQM31ExactLE raw = some value ∧
      exactOperationalChallenge input (.alpha 0) = value := by
  classical
  obtain ⟨_evaluator, _segments, _beforeProducer, _beforeAlpha,
      afterSample, afterBind, _afterBlocks, afterFinal256, _outputs, _advances,
      value, _producerRun, _boundaryRun, _boundaryLookup, _squeezeRun,
      _afterSampleExact, _bindRun, bindLookup, _finalRun, _outputsLength,
      _advancesLength, _coordinates, _terminalExact, _callsExact,
      _accepted, exactDecode, operationalExact, finalLookup, finalNonceLookup,
      q16BaseExact⟩ :=
    exact_compiler_constructs_alpha_zero_prefix_coordinates input
  obtain ⟨actualPrior, actualLater, selectedActor, selectedInput,
      selectedAnswer, selectedDigest, selectedBase, absorbActor, actualRootExact,
      actualTrialExact, selectedPrefix, _prefinalOrigin, selectedBaseExact,
      absorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix input finalTrial
      actualTrial
  have pivotRecordExact :
      (.machineFresh pivotActor pivotInput pivotAnswer : UnifiedExposureRecord) =
        .machineFresh selectedActor selectedInput selectedAnswer := by
    have suppliedAt :
        (exactFixedRootRecords input.package.root)[finalTrial.val]? =
          some (.machineFresh pivotActor pivotInput pivotAnswer :
            UnifiedExposureRecord) := by
      rw [rootExact, trialExact]
      simp
    have actualAt :
        (exactFixedRootRecords input.package.root)[finalTrial.val]? =
          some (.machineFresh selectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) := by
      rw [actualRootExact, actualTrialExact]
      simp
    rw [suppliedAt] at actualAt
    exact Option.some.inj actualAt
  have selectedInputExact : pivotInput = selectedInput := by
    injection pivotRecordExact
  have priorExact : prior = actualPrior :=
    equal_prefixes_of_equal_decomposition_lengths
      (exactFixedRootRecords input.package.root) prior later actualPrior
      actualLater (.machineFresh pivotActor pivotInput pivotAnswer)
      (.machineFresh selectedActor selectedInput selectedAnswer) rootExact
      actualRootExact (by rw [← trialExact, ← actualTrialExact])
  have afterFinalExact : afterFinal256.digest = selectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest input
      afterFinal256.digest selectedDigest
      (exactOperationalRawTrace input).q16BaseDigest selectedBase absorbActor
      (by simpa [q16BaseExact] using finalNonceLookup)
      selectedBaseExact.symm absorbMember
  have selectedDigestExact : canonicalDigest = selectedDigest :=
    literal_prefix_input_eq_fixes_digest canonicalPrefix selectedPrefix
      selectedInputExact
  have finalAnswerExact : afterFinal256.digest = canonicalDigest :=
    afterFinalExact.trans selectedDigestExact.symm
  let finalInput : ShaInput := bytes afterBind.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks (exactOperationalTape input).messages.finalValues
  obtain ⟨finalActor, finalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record input finalInput
      afterFinal256.digest (by simpa [finalInput,
        AspisK1.V7Tag73TranscriptSchedule.Payload.label,
        AspisK1.V7Tag73TranscriptSchedule.Payload.data] using finalLookup)
  have finalMember :
      (.machineFresh finalActor finalInput canonicalDigest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    simpa [finalAnswerExact] using finalMemberRaw
  let canonicalInput : ShaInput := bytes canonicalBefore.digest ++
    [domAbsorb, final256Label] ++
      encodeBlocks (exactOperationalTape input).messages.finalValues
  have canonicalRootMember :
      (.machineFresh canonicalActor canonicalInput canonicalDigest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    rw [rootExact]
    exact List.mem_append_left _ (by simpa [canonicalInput] using canonicalMember)
  have finalInputExact : finalInput = canonicalInput := by
    have recordExact := List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup input) finalMember canonicalRootMember rfl
    injection recordExact
  have afterBindExact : afterBind.digest = canonicalBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) finalInputExact
    simpa [finalInput, canonicalInput] using prefixExact
  let raw := (exactOperationalTape input).messages.challengeValue (.alpha 0)
  let bindInput : ShaInput := bytes afterSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero raw).data
  have bindLookupCommon : tableLookup (exactOperationalTable input) bindInput =
      some canonicalBefore.digest := by
    simpa [bindInput, raw, afterBindExact] using bindLookup
  let boundaryChain : ExactLookupDigestChain (exactOperationalTable input)
      bindInput (fun _ => False) canonicalBefore.digest canonicalBefore.digest :=
    .boundary canonicalBefore.digest bindLookupCommon
  have retained := exact_lookup_digest_chain_retained_before_consumer
    transitionRoom input prior later
      (.machineFresh pivotActor pivotInput pivotAnswer) rootExact boundaryChain
      canonicalInput canonicalDigest canonicalActor
      (by simpa [canonicalInput] using canonicalLookup)
      (by simpa [canonicalInput] using canonicalMember)
      (by simp [canonicalInput, HasLiteralStatePrefix])
  obtain ⟨bindActor, bindMember⟩ :=
    exact_retained_digest_chain_boundary_member retained
  exact ⟨afterSample, raw, value, bindActor, bindLookupCommon,
    by simpa [bindInput] using bindMember, rfl, by simpa [raw] using exactDecode,
    operationalExact⟩

/-- One accepted run retains its alpha binding before the canonical final256
record, and the binding answer is exactly the final256 predecessor state. -/
theorem exact_preQ16_alpha_binding_record_mem_prior
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (witness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample
        foldTrial finalTrial)
    (canonicalBefore : EvalState) (canonicalDigest : Digest256)
    (canonicalActor : QueryActor)
    (canonicalLookup : tableLookup (exactOperationalTable witness.joint.input)
      (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape witness.joint.input).messages.finalValues) =
        some canonicalDigest)
    (canonicalMember :
      (.machineFresh canonicalActor
        (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape witness.joint.input).messages.finalValues)
        canonicalDigest : UnifiedExposureRecord) ∈ witness.joint.prior)
    (canonicalPrefix :
      HasLiteralStatePrefix canonicalDigest witness.joint.pivotInput) :
    ∃ (afterSample : EvalState) (raw : Qm31Bytes) (value : QM31Exact)
        (actor : QueryActor),
      tableLookup (exactOperationalTable witness.joint.input)
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
              raw).data) = some canonicalBefore.digest ∧
      (.machineFresh actor
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
              raw).data) canonicalBefore.digest : UnifiedExposureRecord) ∈
        witness.joint.prior ∧
      raw = (exactOperationalTape witness.joint.input).messages.challengeValue
        (.alpha 0) ∧
      decodeTagQM31ExactLE raw = some value ∧
      exactOperationalChallenge witness.joint.input (.alpha 0) = value := by
  classical
  obtain ⟨_evaluator, _segments, _beforeProducer, _beforeAlpha,
      afterSample, afterBind, _afterBlocks, afterFinal256, _outputs, _advances,
      value, _producerRun, _boundaryRun, _boundaryLookup, _squeezeRun,
      _afterSampleExact, _bindRun, bindLookup, _finalRun, _outputsLength,
      _advancesLength, _coordinates, _terminalExact, _callsExact,
      _accepted, exactDecode, operationalExact, finalLookup, finalNonceLookup,
      q16BaseExact⟩ :=
    exact_compiler_constructs_alpha_zero_prefix_coordinates witness.joint.input
  obtain ⟨_actualPrior, _actualLater, selectedActor, selectedInput,
      selectedAnswer, selectedDigest, selectedBase, absorbActor, actualRootExact,
      actualTrialExact, selectedPrefix, _prefinalOrigin, selectedBaseExact,
      absorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      witness.joint.input finalTrial witness.joint.actualTrial
  have selectedRecordExact :
      (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
          witness.joint.pivotAnswer : UnifiedExposureRecord) =
        .machineFresh selectedActor selectedInput selectedAnswer := by
    have witnessAt :
        (exactFixedRootRecords witness.joint.input.package.root)[finalTrial.val]? =
          some (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
            witness.joint.pivotAnswer : UnifiedExposureRecord) := by
      rw [witness.joint.rootExact, witness.joint.trialExact]
      simp
    have actualAt :
        (exactFixedRootRecords witness.joint.input.package.root)[finalTrial.val]? =
          some (.machineFresh selectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) := by
      rw [actualRootExact, actualTrialExact]
      simp
    rw [witnessAt] at actualAt
    exact Option.some.inj actualAt
  have selectedInputExact : witness.joint.pivotInput = selectedInput := by
    injection selectedRecordExact
  have afterFinalExact : afterFinal256.digest = selectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest witness.joint.input
      afterFinal256.digest selectedDigest
      (exactOperationalRawTrace witness.joint.input).q16BaseDigest selectedBase
      absorbActor (by simpa [q16BaseExact] using finalNonceLookup)
      selectedBaseExact.symm absorbMember
  have selectedDigestExact : canonicalDigest = selectedDigest :=
    literal_prefix_input_eq_fixes_digest canonicalPrefix selectedPrefix
      selectedInputExact
  have finalAnswerExact : afterFinal256.digest = canonicalDigest :=
    afterFinalExact.trans selectedDigestExact.symm
  let finalInput : ShaInput := bytes afterBind.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape witness.joint.input).messages.finalValues
  obtain ⟨finalActor, finalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record witness.joint.input finalInput
      afterFinal256.digest (by simpa [finalInput,
        AspisK1.V7Tag73TranscriptSchedule.Payload.label,
        AspisK1.V7Tag73TranscriptSchedule.Payload.data] using finalLookup)
  have finalMember :
      (.machineFresh finalActor finalInput canonicalDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.joint.input.package.root := by
    simpa [finalAnswerExact] using finalMemberRaw
  let canonicalInput : ShaInput := bytes canonicalBefore.digest ++
    [domAbsorb, final256Label] ++ encodeBlocks
      (exactOperationalTape witness.joint.input).messages.finalValues
  have canonicalRootMember :
      (.machineFresh canonicalActor canonicalInput canonicalDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.joint.input.package.root := by
    rw [witness.joint.rootExact]
    exact List.mem_append_left _ (by simpa [canonicalInput] using canonicalMember)
  have finalInputExact : finalInput = canonicalInput := by
    have recordExact := List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup witness.joint.input) finalMember
        canonicalRootMember rfl
    injection recordExact
  have afterBindExact : afterBind.digest = canonicalBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) finalInputExact
    simpa [finalInput, canonicalInput] using prefixExact
  let raw := (exactOperationalTape witness.joint.input).messages.challengeValue
    (.alpha 0)
  let bindInput : ShaInput := bytes afterSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero raw).data
  have bindLookupCommon : tableLookup
      (exactOperationalTable witness.joint.input) bindInput =
        some canonicalBefore.digest := by
    simpa [bindInput, raw, afterBindExact] using bindLookup
  let boundaryChain : ExactLookupDigestChain
      (exactOperationalTable witness.joint.input) bindInput (fun _ => False)
      canonicalBefore.digest canonicalBefore.digest :=
    .boundary canonicalBefore.digest bindLookupCommon
  have retained := exact_lookup_digest_chain_retained_before_consumer
    transitionRoom witness.joint.input witness.joint.prior witness.joint.later
      (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
        witness.joint.pivotAnswer) witness.joint.rootExact
      boundaryChain
      canonicalInput canonicalDigest canonicalActor
      (by simpa [canonicalInput] using canonicalLookup)
      (by simpa [canonicalInput] using canonicalMember)
      (by simp [canonicalInput, HasLiteralStatePrefix])
  obtain ⟨bindActor, bindMember⟩ :=
    exact_retained_digest_chain_boundary_member retained
  exact ⟨afterSample, raw, value, bindActor, bindLookupCommon,
    by simpa [bindInput] using bindMember, rfl, by simpa [raw] using exactDecode,
    operationalExact⟩

/-- Equal clean prefixes force equal decoded alpha-zero values through the
new explicit binding record. -/
theorem exact_preQ16_clean_pair_alpha_zero_eq_of_binding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
      exactOperationalChallenge rightWitness.joint.input (.alpha 0) := by
  classical
  obtain ⟨leftBefore, rightBefore, canonicalDigest, leftCanonicalActor,
      rightCanonicalActor, canonicalInputExact, leftCanonicalLookup,
      rightCanonicalLookup, leftCanonicalMember, rightCanonicalMember,
      leftCanonicalPrefix, rightCanonicalPrefix⟩ :=
    exact_preQ16_clean_pair_common_final256_record_v2 transitionRoom foldTrial
      finalTrial hidden left right leftWitness rightWitness priorExact
  obtain ⟨leftAfterSample, leftRaw, leftValue, leftBindActor, leftBindLookup,
      leftBindMember, _leftRawExact, leftDecode, leftOperational⟩ :=
    exact_preQ16_alpha_binding_record_mem_prior transitionRoom foldTrial
      finalTrial leftWitness leftBefore canonicalDigest leftCanonicalActor
      leftCanonicalLookup leftCanonicalMember leftCanonicalPrefix
  obtain ⟨rightAfterSample, rightRaw, rightValue, rightBindActor,
      rightBindLookup, rightBindMember, _rightRawExact, rightDecode,
      rightOperational⟩ :=
    exact_preQ16_alpha_binding_record_mem_prior transitionRoom foldTrial
      finalTrial rightWitness rightBefore canonicalDigest rightCanonicalActor
      rightCanonicalLookup rightCanonicalMember rightCanonicalPrefix
  have predecessorExact : leftBefore.digest = rightBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) canonicalInputExact
    simpa using prefixExact
  let leftBindInput : ShaInput := bytes leftAfterSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
        leftRaw).data
  let rightBindInput : ShaInput := bytes rightAfterSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
        rightRaw).data
  have rightBindMemberCommon :
      (.machineFresh rightBindActor rightBindInput leftBefore.digest :
        UnifiedExposureRecord) ∈ leftWitness.joint.prior := by
    rw [priorExact]
    simpa [rightBindInput, predecessorExact] using rightBindMember
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftWitness.joint.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have bindInputExact : leftBindInput = rightBindInput := by
    have recordExact :
        (.machineFresh leftBindActor leftBindInput leftBefore.digest :
            UnifiedExposureRecord) =
          .machineFresh rightBindActor rightBindInput leftBefore.digest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftBindInput] using leftBindMember)
        rightBindMemberCommon rfl
    injection recordExact
  let leftState : MachineState :=
    { digest := leftAfterSample.digest, oracleHistory := [] }
  let rightState : MachineState :=
    { digest := rightAfterSample.digest, oracleHistory := [] }
  let leftBinding : RawChallengeBinding :=
    actualBinding .alphaZero leftRaw
  let rightBinding : RawChallengeBinding :=
    actualBinding .alphaZero rightRaw
  have rawBindingInputExact : rawChallengeBindInput leftState leftBinding =
      rawChallengeBindInput rightState rightBinding := by
    simpa [leftBindInput, rightBindInput, leftState, rightState, leftBinding,
      rightBinding, rawChallengeBindInput, RawChallengeBinding.data,
      actualBinding,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using bindInputExact
  have bindingExact : leftBinding = rightBinding :=
    raw_challenge_bind_input_eq_implies_binding_eq leftState rightState
      leftBinding rightBinding rawBindingInputExact
  have rawExact : leftRaw = rightRaw := by
    simpa [leftBinding, rightBinding, actualBinding] using
      congrArg RawChallengeBinding.value bindingExact
  have valueExact : leftValue = rightValue := by
    apply Option.some.inj
    calc
      some leftValue = decodeTagQM31ExactLE leftRaw := leftDecode.symm
      _ = decodeTagQM31ExactLE rightRaw := by rw [rawExact]
      _ = some rightValue := rightDecode
  exact leftOperational.trans (valueExact.trans rightOperational.symm)

/-- One accepted run retains its gamma binding before the canonical final256
record.  The intervening fold/alpha execution is replayed literally in the
work-erased evaluator. -/
theorem exact_actual_gamma_binding_record_mem_prior
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (actualTrial : ExactFixedK13ActualJointTrial input finalTrial)
    (prior later : List UnifiedExposureRecord)
    (pivotActor : QueryActor) (pivotInput : ShaInput) (pivotAnswer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later)
    (trialExact : finalTrial.val = prior.length)
    (canonicalBefore : EvalState) (canonicalDigest : Digest256)
    (canonicalActor : QueryActor)
    (canonicalLookup : tableLookup (exactOperationalTable input)
      (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks (exactOperationalTape input).messages.finalValues) =
      some canonicalDigest)
    (canonicalMember :
      (.machineFresh canonicalActor
        (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks (exactOperationalTape input).messages.finalValues)
        canonicalDigest : UnifiedExposureRecord) ∈ prior)
    (canonicalPrefix : HasLiteralStatePrefix canonicalDigest pivotInput) :
    ∃ (afterSample afterAlphaSample : EvalState)
        (afterBindDigest : Digest256) (raw : Qm31Bytes) (value : QM31Exact)
        (alphaActor : QueryActor),
      tableLookup (exactOperationalTable input)
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
              raw).data) = some afterBindDigest ∧
      ExactRetainedDigestChain prior
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
              raw).data)
          (IsPostRootStateInput challengeBindLabel) afterBindDigest
            afterAlphaSample.digest ∧
      (.machineFresh alphaActor
          (bytes afterAlphaSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
              ((exactOperationalTape input).messages.challengeValue
                (.alpha 0))).data) canonicalBefore.digest :
            UnifiedExposureRecord) ∈ prior ∧
      raw = (exactOperationalTape input).messages.challengeValue .gamma ∧
      decodeTagQM31ExactLE raw = some value ∧
      exactOperationalChallenge input .gamma = value := by
  classical
  obtain ⟨evaluator, _segments, _beforeGamma, afterGammaSample,
      afterGammaBind, _afterAlphaSample, afterAlphaBind, afterFinal256,
      _afterBlocks, _outputs, value, _prefixRun, _gammaRun, _squeezeRun,
      _afterSampleExact, _accepted, exactDecode, operationalExact, _bindRun,
      gammaBindLookup, middleRun, _alphaBindRun, alphaBindLookup,
      _middleWithAlphaBind, _final256Run, final256Lookup, finalNonceLookup,
      q16BaseExact⟩ :=
    exact_compiler_constructs_accepted_gamma_binding_coordinates input
  obtain ⟨actualPrior, actualLater, selectedActor, selectedInput,
      selectedAnswer, selectedDigest, selectedBase, absorbActor, actualRootExact,
      actualTrialExact, selectedPrefix, _prefinalOrigin, selectedBaseExact,
      absorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix input finalTrial
      actualTrial
  have pivotRecordExact :
      (.machineFresh pivotActor pivotInput pivotAnswer : UnifiedExposureRecord) =
        .machineFresh selectedActor selectedInput selectedAnswer := by
    have suppliedAt :
        (exactFixedRootRecords input.package.root)[finalTrial.val]? =
          some (.machineFresh pivotActor pivotInput pivotAnswer :
            UnifiedExposureRecord) := by
      rw [rootExact, trialExact]
      simp
    have actualAt :
        (exactFixedRootRecords input.package.root)[finalTrial.val]? =
          some (.machineFresh selectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) := by
      rw [actualRootExact, actualTrialExact]
      simp
    rw [suppliedAt] at actualAt
    exact Option.some.inj actualAt
  have selectedInputExact : pivotInput = selectedInput := by
    injection pivotRecordExact
  have _priorExact : prior = actualPrior :=
    equal_prefixes_of_equal_decomposition_lengths
      (exactFixedRootRecords input.package.root) prior later actualPrior
      actualLater (.machineFresh pivotActor pivotInput pivotAnswer)
      (.machineFresh selectedActor selectedInput selectedAnswer) rootExact
      actualRootExact (by rw [← trialExact, ← actualTrialExact])
  have afterFinalExact : afterFinal256.digest = selectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest input
      afterFinal256.digest selectedDigest
      (exactOperationalRawTrace input).q16BaseDigest selectedBase absorbActor
      (by simpa [q16BaseExact] using finalNonceLookup)
      selectedBaseExact.symm absorbMember
  have selectedDigestExact : canonicalDigest = selectedDigest :=
    literal_prefix_input_eq_fixes_digest canonicalPrefix selectedPrefix
      selectedInputExact
  have finalAnswerExact : afterFinal256.digest = canonicalDigest :=
    afterFinalExact.trans selectedDigestExact.symm
  let finalInput : ShaInput := bytes afterAlphaBind.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks (exactOperationalTape input).messages.finalValues
  obtain ⟨finalActor, finalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record input finalInput
      afterFinal256.digest (by simpa [finalInput,
        AspisK1.V7Tag73TranscriptSchedule.Payload.label,
        AspisK1.V7Tag73TranscriptSchedule.Payload.data] using final256Lookup)
  have finalMember :
      (.machineFresh finalActor finalInput canonicalDigest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    simpa [finalAnswerExact] using finalMemberRaw
  let canonicalInput : ShaInput := bytes canonicalBefore.digest ++
    [domAbsorb, final256Label] ++
      encodeBlocks (exactOperationalTape input).messages.finalValues
  have canonicalRootMember :
      (.machineFresh canonicalActor canonicalInput canonicalDigest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    rw [rootExact]
    exact List.mem_append_left _ (by simpa [canonicalInput] using canonicalMember)
  have finalInputExact : finalInput = canonicalInput := by
    have recordExact := List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup input) finalMember canonicalRootMember rfl
    injection recordExact
  have afterAlphaBindExact : afterAlphaBind.digest = canonicalBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) finalInputExact
    simpa [finalInput, canonicalInput] using prefixExact
  let raw := (exactOperationalTape input).messages.challengeValue .gamma
  let bindInput : ShaInput := bytes afterGammaSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma raw).data
  let boundaryChain : ExactLookupDigestChain (exactOperationalTable input)
      bindInput (IsPostRootStateInput challengeBindLabel) afterGammaBind.digest
        afterGammaBind.digest :=
    .boundary afterGammaBind.digest (by simpa [bindInput, raw] using
      gammaBindLookup)
  have middleChain :=
    exact_lookup_digest_chain_through_machine_events_work_erased
      transitionRoom input
      (afterGammaBindBeforeAlphaZeroTailEvents
        (exactOperationalTape input).messages)
      afterGammaBind _afterAlphaSample boundaryChain
      (gamma_middle_events_are_post_challenge_bind
        (exactOperationalTape input).messages) middleRun
  let alphaInput : ShaInput := bytes _afterAlphaSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
        ((exactOperationalTape input).messages.challengeValue (.alpha 0))).data
  have alphaLookupCommon : tableLookup (exactOperationalTable input)
      alphaInput = some canonicalBefore.digest := by
    simpa [alphaInput, afterAlphaBindExact] using alphaBindLookup
  let alphaBoundary : ExactLookupDigestChain (exactOperationalTable input)
      alphaInput (fun _ => False) canonicalBefore.digest
        canonicalBefore.digest :=
    .boundary canonicalBefore.digest alphaLookupCommon
  have alphaRetained := exact_lookup_digest_chain_retained_before_consumer
    transitionRoom input prior later
      (.machineFresh pivotActor pivotInput pivotAnswer) rootExact alphaBoundary
      canonicalInput canonicalDigest canonicalActor
      (by simpa [canonicalInput] using canonicalLookup)
      (by simpa [canonicalInput] using canonicalMember)
      (by simp [canonicalInput, HasLiteralStatePrefix])
  obtain ⟨alphaActor, alphaMember⟩ :=
    exact_retained_digest_chain_boundary_member alphaRetained
  have gammaRetained := exact_lookup_digest_chain_retained_before_consumer
    transitionRoom input prior later
      (.machineFresh pivotActor pivotInput pivotAnswer) rootExact middleChain
      alphaInput canonicalBefore.digest alphaActor alphaLookupCommon alphaMember
      (by simp [alphaInput, HasLiteralStatePrefix])
  exact ⟨afterGammaSample, _afterAlphaSample, afterGammaBind.digest, raw,
    value, alphaActor, by simpa [bindInput, raw] using gammaBindLookup,
    by simpa [bindInput] using gammaRetained,
    by simpa [alphaInput] using alphaMember, rfl,
    by simpa [raw] using exactDecode, operationalExact⟩

theorem exact_preQ16_gamma_binding_record_mem_prior
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (witness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample foldTrial finalTrial)
    (canonicalBefore : EvalState) (canonicalDigest : Digest256)
    (canonicalActor : QueryActor)
    (canonicalLookup : tableLookup (exactOperationalTable witness.joint.input)
      (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
        encodeBlocks
          (exactOperationalTape witness.joint.input).messages.finalValues) =
        some canonicalDigest)
    (canonicalMember :
      (.machineFresh canonicalActor
        (bytes canonicalBefore.digest ++ [domAbsorb, final256Label] ++
          encodeBlocks
            (exactOperationalTape witness.joint.input).messages.finalValues)
        canonicalDigest : UnifiedExposureRecord) ∈ witness.joint.prior)
    (canonicalPrefix :
      HasLiteralStatePrefix canonicalDigest witness.joint.pivotInput) :
    ∃ (afterSample afterAlphaSample : EvalState)
        (afterBindDigest : Digest256) (raw : Qm31Bytes) (value : QM31Exact)
        (alphaActor : QueryActor),
      tableLookup (exactOperationalTable witness.joint.input)
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
              raw).data) = some afterBindDigest ∧
      ExactRetainedDigestChain witness.joint.prior
          (bytes afterSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
              raw).data)
          (IsPostRootStateInput challengeBindLabel) afterBindDigest
            afterAlphaSample.digest ∧
      (.machineFresh alphaActor
          (bytes afterAlphaSample.digest ++ [domAbsorb, challengeBindLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
              ((exactOperationalTape witness.joint.input).messages.challengeValue
                (.alpha 0))).data) canonicalBefore.digest :
            UnifiedExposureRecord) ∈ witness.joint.prior ∧
      raw = (exactOperationalTape witness.joint.input).messages.challengeValue
        .gamma ∧
      decodeTagQM31ExactLE raw = some value ∧
      exactOperationalChallenge witness.joint.input .gamma = value := by
  classical
  obtain ⟨evaluator, _segments, _beforeGamma, afterGammaSample,
      afterGammaBind, _afterAlphaSample, afterAlphaBind, afterFinal256,
      _afterBlocks, _outputs, value, _prefixRun, _gammaRun, _squeezeRun,
      _afterSampleExact, _accepted, exactDecode, operationalExact, _bindRun,
      gammaBindLookup, middleRun, _alphaBindRun, alphaBindLookup,
      _middleWithAlphaBind, _final256Run, final256Lookup, finalNonceLookup,
      q16BaseExact⟩ :=
    exact_compiler_constructs_accepted_gamma_binding_coordinates
      witness.joint.input
  obtain ⟨_actualPrior, _actualLater, selectedActor, selectedInput,
      selectedAnswer, selectedDigest, selectedBase, absorbActor, actualRootExact,
      actualTrialExact, selectedPrefix, _prefinalOrigin, selectedBaseExact,
      absorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      witness.joint.input finalTrial witness.joint.actualTrial
  have selectedRecordExact :
      (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
          witness.joint.pivotAnswer : UnifiedExposureRecord) =
        .machineFresh selectedActor selectedInput selectedAnswer := by
    have witnessAt :
        (exactFixedRootRecords witness.joint.input.package.root)[finalTrial.val]? =
          some (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
            witness.joint.pivotAnswer : UnifiedExposureRecord) := by
      rw [witness.joint.rootExact, witness.joint.trialExact]
      simp
    have actualAt :
        (exactFixedRootRecords witness.joint.input.package.root)[finalTrial.val]? =
          some (.machineFresh selectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) := by
      rw [actualRootExact, actualTrialExact]
      simp
    rw [witnessAt] at actualAt
    exact Option.some.inj actualAt
  have selectedInputExact : witness.joint.pivotInput = selectedInput := by
    injection selectedRecordExact
  have afterFinalExact : afterFinal256.digest = selectedDigest :=
    final_nonce_lookup_and_root_record_fix_digest witness.joint.input
      afterFinal256.digest selectedDigest
      (exactOperationalRawTrace witness.joint.input).q16BaseDigest selectedBase
      absorbActor (by simpa [q16BaseExact] using finalNonceLookup)
      selectedBaseExact.symm absorbMember
  have selectedDigestExact : canonicalDigest = selectedDigest :=
    literal_prefix_input_eq_fixes_digest canonicalPrefix selectedPrefix
      selectedInputExact
  have finalAnswerExact : afterFinal256.digest = canonicalDigest :=
    afterFinalExact.trans selectedDigestExact.symm
  let finalInput : ShaInput := bytes afterAlphaBind.digest ++ [domAbsorb,
    final256Label] ++ encodeBlocks
      (exactOperationalTape witness.joint.input).messages.finalValues
  obtain ⟨finalActor, finalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record witness.joint.input finalInput
      afterFinal256.digest (by simpa [finalInput,
        AspisK1.V7Tag73TranscriptSchedule.Payload.label,
        AspisK1.V7Tag73TranscriptSchedule.Payload.data] using final256Lookup)
  have finalMember :
      (.machineFresh finalActor finalInput canonicalDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.joint.input.package.root := by
    simpa [finalAnswerExact] using finalMemberRaw
  let canonicalInput : ShaInput := bytes canonicalBefore.digest ++
    [domAbsorb, final256Label] ++ encodeBlocks
      (exactOperationalTape witness.joint.input).messages.finalValues
  have canonicalRootMember :
      (.machineFresh canonicalActor canonicalInput canonicalDigest :
        UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.joint.input.package.root := by
    rw [witness.joint.rootExact]
    exact List.mem_append_left _ (by simpa [canonicalInput] using canonicalMember)
  have finalInputExact : finalInput = canonicalInput := by
    have recordExact := List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup witness.joint.input) finalMember
        canonicalRootMember rfl
    injection recordExact
  have afterAlphaBindExact : afterAlphaBind.digest = canonicalBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) finalInputExact
    simpa [finalInput, canonicalInput] using prefixExact
  let raw := (exactOperationalTape witness.joint.input).messages.challengeValue
    .gamma
  let bindInput : ShaInput := bytes afterGammaSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma raw).data
  let boundaryChain : ExactLookupDigestChain
      (exactOperationalTable witness.joint.input) bindInput
      (IsPostRootStateInput challengeBindLabel) afterGammaBind.digest
        afterGammaBind.digest :=
    .boundary afterGammaBind.digest (by simpa [bindInput, raw] using
      gammaBindLookup)
  have middleChain :=
    exact_lookup_digest_chain_through_machine_events_work_erased
      transitionRoom witness.joint.input
      (afterGammaBindBeforeAlphaZeroTailEvents
        (exactOperationalTape witness.joint.input).messages)
      afterGammaBind _afterAlphaSample boundaryChain
      (gamma_middle_events_are_post_challenge_bind
        (exactOperationalTape witness.joint.input).messages)
      middleRun
  let alphaInput : ShaInput := bytes _afterAlphaSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
        ((exactOperationalTape witness.joint.input).messages.challengeValue
          (.alpha 0))).data
  have alphaLookupCommon : tableLookup
      (exactOperationalTable witness.joint.input) alphaInput =
        some canonicalBefore.digest := by
    simpa [alphaInput, afterAlphaBindExact] using alphaBindLookup
  let alphaBoundary : ExactLookupDigestChain
      (exactOperationalTable witness.joint.input) alphaInput (fun _ => False)
      canonicalBefore.digest canonicalBefore.digest :=
    .boundary canonicalBefore.digest alphaLookupCommon
  have alphaRetained := exact_lookup_digest_chain_retained_before_consumer
    transitionRoom witness.joint.input witness.joint.prior witness.joint.later
      (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
        witness.joint.pivotAnswer) witness.joint.rootExact alphaBoundary
      canonicalInput canonicalDigest canonicalActor
      (by simpa [canonicalInput] using canonicalLookup)
      (by simpa [canonicalInput] using canonicalMember)
      (by simp [canonicalInput, HasLiteralStatePrefix])
  obtain ⟨alphaActor, alphaMember⟩ :=
    exact_retained_digest_chain_boundary_member alphaRetained
  have gammaRetained := exact_lookup_digest_chain_retained_before_consumer
    transitionRoom witness.joint.input witness.joint.prior witness.joint.later
      (.machineFresh witness.joint.pivotActor witness.joint.pivotInput
        witness.joint.pivotAnswer) witness.joint.rootExact middleChain alphaInput
      canonicalBefore.digest alphaActor alphaLookupCommon alphaMember
      (by simp [alphaInput, HasLiteralStatePrefix])
  exact ⟨afterGammaSample, _afterAlphaSample, afterGammaBind.digest, raw,
    value, alphaActor,
    by simpa [bindInput, raw] using gammaBindLookup,
    by simpa [bindInput] using gammaRetained,
    by simpa [alphaInput] using alphaMember, rfl,
    by simpa [raw] using exactDecode, operationalExact⟩

/-- Equal clean prefixes force equal decoded gamma values through the explicit
gamma binding record. -/
theorem exact_preQ16_clean_pair_operational_gamma_eq_of_binding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    exactOperationalChallenge leftWitness.joint.input .gamma =
      exactOperationalChallenge rightWitness.joint.input .gamma := by
  classical
  obtain ⟨leftBefore, rightBefore, canonicalDigest, leftCanonicalActor,
      rightCanonicalActor, canonicalInputExact, leftCanonicalLookup,
      rightCanonicalLookup, leftCanonicalMember, rightCanonicalMember,
      leftCanonicalPrefix, rightCanonicalPrefix⟩ :=
    exact_preQ16_clean_pair_common_final256_record_v2 transitionRoom foldTrial
      finalTrial hidden left right leftWitness rightWitness priorExact
  obtain ⟨leftAfterSample, leftAfterAlphaSample, leftAfterBind, leftRaw,
      leftValue, leftAlphaActor, leftBindLookup, leftChain, leftAlphaMember,
      _leftRawExact, leftDecode, leftOperational⟩ :=
    exact_preQ16_gamma_binding_record_mem_prior transitionRoom foldTrial
      finalTrial leftWitness leftBefore canonicalDigest leftCanonicalActor
      leftCanonicalLookup leftCanonicalMember leftCanonicalPrefix
  obtain ⟨rightAfterSample, rightAfterAlphaSample, rightAfterBind, rightRaw,
      rightValue, rightAlphaActor, rightBindLookup, rightChain,
      rightAlphaMember, _rightRawExact, rightDecode, rightOperational⟩ :=
    exact_preQ16_gamma_binding_record_mem_prior transitionRoom foldTrial
      finalTrial rightWitness rightBefore canonicalDigest rightCanonicalActor
      rightCanonicalLookup rightCanonicalMember rightCanonicalPrefix
  let leftBindInput : ShaInput := bytes leftAfterSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
        leftRaw).data
  let rightBindInput : ShaInput := bytes rightAfterSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
        rightRaw).data
  let leftAlphaInput : ShaInput := bytes leftAfterAlphaSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
        ((exactOperationalTape leftWitness.joint.input).messages.challengeValue
          (.alpha 0))).data
  let rightAlphaInput : ShaInput := bytes rightAfterAlphaSample.digest ++
    [domAbsorb, challengeBindLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .alphaZero
        ((exactOperationalTape rightWitness.joint.input).messages.challengeValue
          (.alpha 0))).data
  have predecessorExact : leftBefore.digest = rightBefore.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) canonicalInputExact
    simpa using prefixExact
  have rightAlphaMemberCommon :
      (.machineFresh rightAlphaActor rightAlphaInput leftBefore.digest :
        UnifiedExposureRecord) ∈ leftWitness.joint.prior := by
    rw [priorExact]
    simpa [rightAlphaInput, predecessorExact] using rightAlphaMember
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftWitness.joint.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have alphaInputExact : leftAlphaInput = rightAlphaInput := by
    have recordExact :
        (.machineFresh leftAlphaActor leftAlphaInput leftBefore.digest :
            UnifiedExposureRecord) =
          .machineFresh rightAlphaActor rightAlphaInput leftBefore.digest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftAlphaInput] using leftAlphaMember)
        rightAlphaMemberCommon rfl
    injection recordExact
  have terminalExact : leftAfterAlphaSample.digest =
      rightAfterAlphaSample.digest := by
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) alphaInputExact
    simpa [leftAlphaInput, rightAlphaInput] using prefixExact
  have rightChainCommon : ExactRetainedDigestChain leftWitness.joint.prior
      rightBindInput (IsPostRootStateInput challengeBindLabel) rightAfterBind
        leftAfterAlphaSample.digest := by
    dsimp only [rightBindInput]
    rw [priorExact]
    simpa [terminalExact] using rightChain
  have leftBoundaryAvoids : ∀ input,
      IsPostRootStateInput challengeBindLabel input →
        leftBindInput ≠ input := by
    apply absorb_input_avoids_post_root_state_input challengeBindLabel
      leftAfterSample.digest
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
        leftRaw).data
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have rightBoundaryAvoids : ∀ input,
      IsPostRootStateInput challengeBindLabel input →
        rightBindInput ≠ input := by
    apply absorb_input_avoids_post_root_state_input challengeBindLabel
      rightAfterSample.digest
      (AspisK1.V7Tag73TranscriptSchedule.Payload.challengeBind .gamma
        rightRaw).data
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have bindInputExact : leftBindInput = rightBindInput :=
    exact_retained_digest_chains_boundary_input_eq priorAnswersNodup
      (by simpa [leftBindInput] using leftChain)
      (by simpa [rightBindInput] using rightChainCommon)
      (by simpa [leftBindInput] using leftBoundaryAvoids)
      (by simpa [rightBindInput] using rightBoundaryAvoids)
  let leftState : MachineState :=
    { digest := leftAfterSample.digest, oracleHistory := [] }
  let rightState : MachineState :=
    { digest := rightAfterSample.digest, oracleHistory := [] }
  let leftBinding := actualBinding .gamma leftRaw
  let rightBinding := actualBinding .gamma rightRaw
  have bindingInputExact : rawChallengeBindInput leftState leftBinding =
      rawChallengeBindInput rightState rightBinding := by
    simpa [leftBindInput, rightBindInput, leftState, rightState, leftBinding,
      rightBinding, rawChallengeBindInput, RawChallengeBinding.data,
      actualBinding,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using bindInputExact
  have bindingExact := raw_challenge_bind_input_eq_implies_binding_eq
    leftState rightState leftBinding rightBinding bindingInputExact
  have rawExact : leftRaw = rightRaw := by
    simpa [leftBinding, rightBinding, actualBinding] using
      congrArg RawChallengeBinding.value bindingExact
  have valueExact : leftValue = rightValue := by
    apply Option.some.inj
    calc
      some leftValue = decodeTagQM31ExactLE leftRaw := leftDecode.symm
      _ = decodeTagQM31ExactLE rightRaw := by rw [rawExact]
      _ = some rightValue := rightDecode
  exact leftOperational.trans (valueExact.trans rightOperational.symm)

/-- The two explicit decoded-value bindings discharge the exact alpha/gamma
endpoint required by the corrected pre-q16 profile. -/
theorem exact_preQ16_clean_pair_alpha_gamma_invariant_of_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap) :
    ExactPreQ16CleanK13PairAlphaGammaInvariantOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness
    _actorExact contextExact foldExact _workExact
  have priorExact := exact_preQ16_clean_pair_selected_priors_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness programmedCover
      contextExact foldExact
  have alphaExact := exact_preQ16_clean_pair_alpha_zero_eq_of_binding
    transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness priorExact
  have operationalGamma :=
    exact_preQ16_clean_pair_operational_gamma_eq_of_binding transitionRoom
      foldTrial finalTrial hidden left right leftWitness rightWitness priorExact
  obtain ⟨_leftDecoded, _leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.joint.input
  obtain ⟨_rightDecoded, _rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.joint.input
  have gammaExact := leftBinding.gammaExact.trans
    (operationalGamma.trans rightBinding.gammaExact.symm)
  exact ⟨alphaExact, gammaExact⟩

/-- Complete corrected K1.3 coordinate invariance, ready for the already
proved one-forest probability wrapper. -/
theorem exact_preQ16_clean_pair_coordinate_invariant_of_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap) :
    ExactPreQ16CleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  have alphaGamma := exact_preQ16_clean_pair_alpha_gamma_invariant_of_bindings
    (decoder := decoder) source transitionRoom programmedCover
  have operational := exact_preQ16_clean_pair_operational_remaining_of_alpha_gamma
    source transitionRoom programmedCover alphaGamma
  have remaining := exact_preQ16_clean_pair_remaining_of_operational
    source operational
  have adversary := exact_preQ16_clean_pair_adversary_semantic_of_remaining
    transitionRoom programmedCover remaining
  have semantic := exact_preQ16_clean_pair_semantic_invariant_of_adversary_anchors
    programmedCover adversary
  exact exact_preQ16_clean_k13_pair_coordinate_invariant_of_semantic semantic

/-- Release-facing corrected K1.3 probability result with no residual
alpha/gamma invariant premise. -/
theorem exact_clean_preQ16_trial_union_probability_le_one_forest_of_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          ⋃ finalTrial : ExactCompilerExposureTrial parameters,
            exactPreQ16K13JointTrialEvent transitionFuel configuration projection
              fixedInstance decoder finalTrial) ≤
      q16SemanticOneForestRawError := by
  exact exact_clean_preQ16_trial_union_probability_le_one_forest hiddenLaw
    transitionRoom programmedCover frontierExact
      (exact_preQ16_clean_pair_coordinate_invariant_of_bindings source
        transitionRoom programmedCover)
      reference traceExists foldExposureCap finalExposureCap

#print axioms exact_preQ16_clean_pair_common_final256_record_v2
#print axioms exact_actual_alpha_binding_record_mem_prior
#print axioms exact_actual_gamma_binding_record_mem_prior
#print axioms exact_preQ16_alpha_binding_record_mem_prior
#print axioms exact_preQ16_clean_pair_alpha_zero_eq_of_binding
#print axioms exact_preQ16_gamma_binding_record_mem_prior
#print axioms exact_preQ16_clean_pair_operational_gamma_eq_of_binding
#print axioms exact_preQ16_clean_pair_alpha_gamma_invariant_of_bindings
#print axioms exact_preQ16_clean_pair_coordinate_invariant_of_bindings
#print axioms
  exact_clean_preQ16_trial_union_probability_le_one_forest_of_bindings

end

end AspisK1.V7Tag73K13BoundChallengeClosure

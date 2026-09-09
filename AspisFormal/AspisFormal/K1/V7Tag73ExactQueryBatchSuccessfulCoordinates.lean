import AspisFormal.K1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin

/-!
# Exact successful coordinates for the deployed query-batch sampler

The accepted Tag-73 execution contains a bounded nonzero QM31 sampler after
the q16 forest.  The root-order modules identify every consumed SHA answer;
this file identifies the same consumed prefix with the successful sampler
factor used by the finite-field probability theorem.  In particular, the
factor's returned value is exactly the operational query-batch challenge.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactQueryBatchSuccessfulCoordinates

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A fixed oracle table and initial duplex state determine a root-ordered
chain uniquely once its length is fixed.  This is table functionality, not a
SHA injectivity assumption. -/
theorem exact_root_ordered_q16_chain_unique_of_length
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {producerInput : ShaInput} {initialDigest : Digest256}
    {leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256}
    (left : ExactRootOrderedQ16Chain input producerInput initialDigest
      leftOutputs leftAdvances)
    (right : ExactRootOrderedQ16Chain input producerInput initialDigest
      rightOutputs rightAdvances)
    (lengthExact : leftOutputs.length = rightOutputs.length) :
    leftOutputs = rightOutputs ∧ leftAdvances = rightAdvances := by
  induction left generalizing rightOutputs rightAdvances with
  | done =>
      cases right with
      | done => exact ⟨rfl, rfl⟩
      | next => simp at lengthExact
  | @next producerInput digest leftOutput leftAdvance leftOutputs leftAdvances
      producerFound leftOutputFound leftAdvanceFound _ _ leftTail ih =>
      cases right with
      | done => simp at lengthExact
      | @next _ _ rightOutput rightAdvance rightOutputs rightAdvances
          _ rightOutputFound rightAdvanceFound _ _ rightTail =>
          have outputExact : leftOutput = rightOutput :=
            Option.some.inj (leftOutputFound.symm.trans rightOutputFound)
          have advanceExact : leftAdvance = rightAdvance :=
            Option.some.inj (leftAdvanceFound.symm.trans rightAdvanceFound)
          subst rightOutput
          subst rightAdvance
          have tailLength : leftOutputs.length = rightOutputs.length := by
            simpa using Nat.succ.inj lengthExact
          obtain ⟨outputsExact, advancesExact⟩ := ih rightTail tailLength
          exact ⟨congrArg (List.cons leftOutput) outputsExact,
            congrArg (List.cons leftAdvance) advancesExact⟩

/-- The literal query-batch sampler consumed by an accepted production run is
a successful bounded nonzero-QM31 tape, and its factorized value is exactly
the challenge used by the operational verifier.  Only the unread suffix is
zero padded. -/
theorem exact_operational_query_batch_constructs_successful_coordinates
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (producerInput : ShaInput) (initialDigest : Digest256)
      (outputs advances : List Digest256)
      (flat : SuccessfulGammaPrefixTape)
      (decoded consumedDecoded : OrdinaryPrefixDecode)
      (consumedValue : QM31Exact),
      tableLookup (exactOperationalTable input) producerInput =
          some initialDigest ∧
      (∃ beforeDomain : EvalState,
        producerInput = bytes beforeDomain.digest ++
          [domAbsorb, queryBatchChallengeLabel] ∧
        beforeDomain.digest =
          (exactOperationalQ16Evaluator input).afterQ16.digest) ∧
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
        advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse
          .queryBatch).blocksUsed ∧
      advances.length = outputs.length ∧
      (gammaOutputBlocks flat.1).take outputs.length = outputs ∧
      (List.ofFn flat.1.2).take advances.length = advances ∧
      decodeNonzeroPrefix 3 outputs = some consumedDecoded ∧
      decodeTagQM31ExactLE consumedDecoded.value = some consumedValue ∧
      consumedDecoded.value =
        (exactOperationalTape input).messages.challengeValue .queryBatch ∧
      runGammaPrefix flat.1 = some decoded ∧
      decoded.value =
        (exactOperationalTape input).messages.challengeValue .queryBatch ∧
      exactOperationalChallenge input .queryBatch = consumedValue ∧
      exactOperationalChallenge input .queryBatch =
        (routedSuccessfulGammaValue
          (successfulGammaPrefixFlatRoutingEquiv flat)).1 := by
  let evaluator := exactOperationalQ16Evaluator input
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  have splitRun := evaluator.afterQ16Run
  rw [after_accepted_query_scan_query_batch_split] at splitRun
  obtain ⟨beforeQueryBatch, prefixRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) beforeQueryBatchChallengeEvents
      (challengeEvent (exactOperationalTape input).messages .queryBatch ::
        afterQueryBatchChallengeEvents
          (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState).mp splitRun
  obtain ⟨beforeDomain, frontierRun, domainRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) [.check .frontierCount]
      [.absorb .queryBatchDomain] evaluator.afterQ16 beforeQueryBatch).mp
        (by simpa [beforeQueryBatchChallengeEvents] using prefixRun)
  simp only [runMachineEventsWorkErased] at domainRun
  obtain ⟨afterDomain, absorbRun, domainDone⟩ :=
    Option.bind_eq_some_iff.mp domainRun
  have afterDomainExact : afterDomain = beforeQueryBatch := by
    simpa [runMachineEventsWorkErased] using Option.some.inj domainDone
  subst afterDomain
  have beforeDomainStart : beforeDomain.digest =
      (exactOperationalQ16Evaluator input).afterQ16.digest := by
    have exact : evaluator.afterQ16 = beforeDomain := by
      simpa [runMachineEventsWorkErased, runMachineEventWorkErased] using
        frontierRun
    simpa using congrArg EvalState.digest exact.symm
  let producerInput : ShaInput :=
    bytes beforeDomain.digest ++ [domAbsorb, queryBatchChallengeLabel]
  have producerLookup : tableLookup (exactOperationalTable input)
      producerInput = some beforeQueryBatch.digest := by
    have lookup := absorb_step_exposes_literal_lookup
      (exactOperationalTable input) beforeDomain beforeQueryBatch
        .queryBatchDomain absorbRun
    simpa [producerInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using lookup
  simp only [runMachineEventsWorkErased] at restRun
  obtain ⟨afterQueryBatch, queryBatchRun, tailRun⟩ :=
    Option.bind_eq_some_iff.mp restRun
  have queryBatchRun' : runMachineEventWorkErased
      (exactOperationalTable input) beforeQueryBatch
      (.challenge .queryBatch
        ((exactOperationalTape input).messages.challengeUse .queryBatch)) =
        some afterQueryBatch := by
    simpa [challengeEvent] using queryBatchRun
  obtain ⟨outputs, afterBlocks, squeezeRun, _afterExact, outputsLength,
      recordMember⟩ := challenge_event_work_erased_exposes_record
    (exactOperationalTable input) beforeQueryBatch afterQueryBatch .queryBatch
      ((exactOperationalTape input).messages.challengeUse .queryBatch)
      queryBatchRun'
  obtain ⟨advances, advancesLength, coordinates, _callsExact⟩ :=
    squeeze_many_coordinates (exactOperationalTable input)
      (.challenge .queryBatch)
      ((exactOperationalTape input).messages.challengeUse
        .queryBatch).blocksUsed beforeQueryBatch afterBlocks outputs squeezeRun
  have ordered : ExactRootOrderedQ16Chain input producerInput
      beforeQueryBatch.digest outputs advances :=
    gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
      producerInput beforeQueryBatch.digest producerLookup coordinates
  have recordFinal :
      ({ id := .queryBatch, blocks := outputs } : SampleRecord) ∈
        evaluator.finalState.samples :=
    machine_events_work_erased_samples_included (exactOperationalTable input)
      (afterQueryBatchChallengeEvents (exactOperationalTape input).messages)
      afterQueryBatch evaluator.finalState tailRun _ recordMember
  have acceptedParameter :
      decodeNonzeroExact outputs =
        some ((exactOperationalTape input).messages.challengeValue
          .queryBatch) := by
    have decodedAtFinal := finalDecoded
      ({ id := .queryBatch, blocks := outputs } : SampleRecord) recordFinal
    simpa [decodeChallengeParameter, samplerMode] using decodedAtFinal
  obtain ⟨consumedDecoded, prefixRun, _noRemaining, decodedValue⟩ :=
    decodeNonzeroExact_witness outputs
      ((exactOperationalTape input).messages.challengeValue .queryBatch)
      acceptedParameter
  have outputsWithin : outputs.length ≤ 12 := by
    rw [outputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        .queryBatch).withinDeployedCap
  have advancesWithin : advances.length ≤ 12 := by
    rw [advancesLength]
    exact outputsWithin
  let tape := totalGammaTapeOfConsumed outputs advances (zeroBytes 32)
    (zeroBytes 32)
  have outputPrefix : (gammaOutputBlocks tape).take outputs.length = outputs :=
    total_gamma_tape_output_prefix outputs advances (zeroBytes 32)
      (zeroBytes 32) outputsWithin
  let unreadOutputs := (gammaOutputBlocks tape).drop outputs.length
  have outputSplit : gammaOutputBlocks tape = outputs ++ unreadOutputs := by
    calc
      gammaOutputBlocks tape =
          (gammaOutputBlocks tape).take outputs.length ++
            (gammaOutputBlocks tape).drop outputs.length :=
        (List.take_append_drop outputs.length (gammaOutputBlocks tape)).symm
      _ = outputs ++ unreadOutputs := by rw [outputPrefix]
  have fullPrefixRun : runGammaPrefix tape =
      some (appendOrdinaryRemaining consumedDecoded unreadOutputs) := by
    unfold runGammaPrefix
    rw [outputSplit]
    exact decodeNonzeroPrefix_append_of_some 3 outputs unreadOutputs
      consumedDecoded prefixRun
  let flat : SuccessfulGammaPrefixTape :=
    ⟨tape, by unfold GammaPrefixSucceeds; rw [fullPrefixRun]; rfl⟩
  have flatRun : runGammaPrefix flat.1 =
      some (appendOrdinaryRemaining consumedDecoded unreadOutputs) :=
    fullPrefixRun
  have routedDecode := flatRoutingEquiv_returned_exact_value flat
    (appendOrdinaryRemaining consumedDecoded unreadOutputs) flatRun
  obtain ⟨exactValue, exactDecode⟩ :=
    decodeChallengeParameter_has_exact_tower_value
      exactSecureCircleParameterMap .queryBatch outputs
      ((exactOperationalTape input).messages.challengeValue .queryBatch)
      (by simpa [decodeChallengeParameter, samplerMode] using acceptedParameter)
  have operationalValue : exactOperationalChallenge input .queryBatch =
      exactValue := by
    simp [exactOperationalChallenge, exactChallengeValue, exactDecode]
  have routedValue :
      (routedSuccessfulGammaValue
        (successfulGammaPrefixFlatRoutingEquiv flat)).1 = exactValue := by
    apply Option.some.inj
    rw [← routedDecode]
    simpa [appendOrdinaryRemaining, decodedValue] using exactDecode
  refine ⟨producerInput, beforeQueryBatch.digest, outputs, advances, flat,
    appendOrdinaryRemaining consumedDecoded unreadOutputs, consumedDecoded,
    exactValue, producerLookup, ⟨beforeDomain, rfl, beforeDomainStart⟩,
    ordered, outputsLength, advancesLength,
    outputPrefix, ?_, prefixRun, ?_, decodedValue, flatRun, ?_, operationalValue,
    ?_⟩
  · exact total_gamma_tape_advance_prefix outputs advances (zeroBytes 32)
      (zeroBytes 32) advancesWithin
  · simpa [decodedValue] using exactDecode
  · simpa [appendOrdinaryRemaining] using decodedValue
  · exact operationalValue.trans routedValue.symm

/-- Any root-ordered chain at the canonical post-q16 query-batch boundary and
with the deployed block count is the consumed sampler chain above.  This lets
the causal-router theorem use its own source-selected witnesses without
depending on existential witness identity. -/
theorem exact_query_batch_ordered_chain_has_successful_coordinates
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    {producerInput : ShaInput} {initialDigest : Digest256}
    {outputs advances : List Digest256}
    (producerOrigin : ∃ beforeDomain : EvalState,
      producerInput = bytes beforeDomain.digest ++
        [domAbsorb, queryBatchChallengeLabel] ∧
      beforeDomain.digest =
        (exactOperationalQ16Evaluator input).afterQ16.digest)
    (chain : ExactRootOrderedQ16Chain input producerInput initialDigest outputs
      advances)
    (outputsLength : outputs.length =
      ((exactOperationalTape input).messages.challengeUse
        .queryBatch).blocksUsed) :
    ∃ (flat : SuccessfulGammaPrefixTape)
      (decoded consumedDecoded : OrdinaryPrefixDecode)
      (consumedValue : QM31Exact),
      (gammaOutputBlocks flat.1).take outputs.length = outputs ∧
      (List.ofFn flat.1.2).take advances.length = advances ∧
      decodeNonzeroPrefix 3 outputs = some consumedDecoded ∧
      decodeTagQM31ExactLE consumedDecoded.value = some consumedValue ∧
      consumedDecoded.value =
        (exactOperationalTape input).messages.challengeValue .queryBatch ∧
      runGammaPrefix flat.1 = some decoded ∧
      decoded.value =
        (exactOperationalTape input).messages.challengeValue .queryBatch ∧
      exactOperationalChallenge input .queryBatch = consumedValue ∧
      exactOperationalChallenge input .queryBatch =
        (routedSuccessfulGammaValue
          (successfulGammaPrefixFlatRoutingEquiv flat)).1 := by
  obtain ⟨sourceInput, sourceDigest, sourceOutputs, sourceAdvances, flat,
      decoded, consumedDecoded, consumedValue, sourceLookup, sourceOrigin,
      sourceChain, sourceOutputsLength, _sourceAdvancesLength, outputPrefix,
      advancePrefix, prefixRun, exactDecode, decodedValue, flatRun,
      finalDecodedValue, operationalValue, challengeExact⟩ :=
    exact_operational_query_batch_constructs_successful_coordinates
      transitionRoom input
  obtain ⟨leftBefore, leftInput, leftStart⟩ := producerOrigin
  obtain ⟨rightBefore, rightInput, rightStart⟩ := sourceOrigin
  have beforeDigestExact : leftBefore.digest = rightBefore.digest :=
    leftStart.trans rightStart.symm
  have producerInputExact : producerInput = sourceInput := by
    rw [leftInput, rightInput, beforeDigestExact]
  rw [← producerInputExact] at sourceLookup sourceChain
  have inputLookup := exact_root_ordered_q16_chain_producer_lookup chain
  have initialDigestExact : initialDigest = sourceDigest :=
    Option.some.inj (inputLookup.symm.trans sourceLookup)
  rw [← initialDigestExact] at sourceChain
  have chainLength : outputs.length = sourceOutputs.length :=
    outputsLength.trans sourceOutputsLength.symm
  obtain ⟨outputsExact, advancesExact⟩ :=
    exact_root_ordered_q16_chain_unique_of_length chain sourceChain chainLength
  exact ⟨flat, decoded, consumedDecoded, consumedValue,
    by simpa [outputsExact] using outputPrefix,
    by simpa [advancesExact] using advancePrefix,
    by simpa [outputsExact] using prefixRun,
    exactDecode, decodedValue, flatRun, finalDecodedValue, operationalValue,
    challengeExact⟩

#print axioms exact_operational_query_batch_constructs_successful_coordinates
#print axioms exact_root_ordered_q16_chain_unique_of_length
#print axioms exact_query_batch_ordered_chain_has_successful_coordinates

end
end AspisK1.V7Tag73ExactQueryBatchSuccessfulCoordinates

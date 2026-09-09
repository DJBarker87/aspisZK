import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchFullRouting

/-!
# Probability-ready deployed query-batch coordinate

The complete production routing theorem names every consumed query-batch
output in the 542-slot causal coordinate system.  This module turns those
pointwise routing facts into the exact successful nonzero-field sampler tape
used by the finite probability theorem.  No unconsumed suffix value is
constrained or trusted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedQueryBatchProbabilityReady

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchFullRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The deployed accepted execution selects one fold-work trial, one
final-work trial and one q16 terminal candidate such that the query-batch
component of their 542-coordinate router succeeds and returns exactly the
operational batching challenge. -/
theorem exact_selected_fold_armed_query_batch_coordinate_is_successful
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
        (target : Q16DigestSlot),
      let router := exactCompilerFoldArmedCandidateQueryBatchRouter parameters
        transitionFuel foldTrial.val finalTrial.val target
        (exactPlainRomCursor configuration sample.1).erase
      let coordinates :=
        exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
          router sample.2
      ∃ success : GammaPrefixSucceeds coordinates.2,
        exactOperationalChallenge input .queryBatch =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv
              ⟨coordinates.2, success⟩)).1 := by
  obtain ⟨foldTrial, finalTrial, target, outputs, advances, _flat,
      consumedDecoded, consumedValue, outputsLength, _advancesLength,
      _flatOutputPrefix, _flatAdvancePrefix, prefixRun, exactDecode,
      operationalValue, _flatChallenge, outputRouted, _advanceRouted⟩ :=
    exact_selected_fold_armed_candidate_query_batch_is_fully_routed
      transitionRoom programmedCover input
  let router := exactCompilerFoldArmedCandidateQueryBatchRouter parameters
    transitionFuel foldTrial.val finalTrial.val target
    (exactPlainRomCursor configuration sample.1).erase
  let coordinates :=
    exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router sample.2
  have outputsWithin : outputs.length ≤ 12 := by
    rw [outputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        .queryBatch).withinDeployedCap
  have outputPrefix :
      (gammaOutputBlocks coordinates.2).take outputs.length = outputs := by
    apply List.ext_getElem
    · simp [gammaOutputBlocks, outputsWithin]
    · intro index leftBound rightBound
      have indexWithin : index < 12 := rightBound.trans_le outputsWithin
      let slot : Fin 12 := ⟨index, indexWithin⟩
      obtain ⟨routedSlot, slotValue, routed⟩ :=
        outputRouted index rightBound
      have routedSlotExact : routedSlot = slot := by
        apply Fin.ext
        simpa [slot] using slotValue
      subst routedSlot
      have coordinateExact := coordinate_eq_of_causalRoutedAnswer?_eq_some
        router
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2))
        (Sum.inr (slot, false)) (Finset.mem_univ _) outputs[index] routed
      have publicExact :=
        fold_alpha_q16_query_batch_output_coordinate_eq_named_slot parameters
          router sample.2 slot
      simp only [List.getElem_take, gammaOutputBlocks, List.getElem_ofFn]
      exact publicExact.trans coordinateExact
  let unreadOutputs :=
    (gammaOutputBlocks coordinates.2).drop outputs.length
  have outputSplit :
      gammaOutputBlocks coordinates.2 = outputs ++ unreadOutputs := by
    calc
      gammaOutputBlocks coordinates.2 =
          (gammaOutputBlocks coordinates.2).take outputs.length ++
            (gammaOutputBlocks coordinates.2).drop outputs.length :=
        (List.take_append_drop outputs.length
          (gammaOutputBlocks coordinates.2)).symm
      _ = outputs ++ unreadOutputs := by rw [outputPrefix]
  have fullRun : runGammaPrefix coordinates.2 =
      some (appendOrdinaryRemaining consumedDecoded unreadOutputs) := by
    unfold runGammaPrefix
    rw [outputSplit]
    exact decodeNonzeroPrefix_append_of_some 3 outputs unreadOutputs
      consumedDecoded prefixRun
  have success : GammaPrefixSucceeds coordinates.2 := by
    unfold GammaPrefixSucceeds
    rw [fullRun]
    rfl
  let successful : SuccessfulGammaPrefixTape := ⟨coordinates.2, success⟩
  have routedDecode := flatRoutingEquiv_returned_exact_value successful
    (appendOrdinaryRemaining consumedDecoded unreadOutputs) fullRun
  have routedValue :
      (routedSuccessfulGammaValue
        (successfulGammaPrefixFlatRoutingEquiv successful)).1 =
          consumedValue := by
    apply Option.some.inj
    rw [← routedDecode]
    simpa [appendOrdinaryRemaining] using exactDecode
  exact ⟨foldTrial, finalTrial, target, success,
    operationalValue.trans routedValue.symm⟩

#print axioms exact_selected_fold_armed_query_batch_coordinate_is_successful

end
end AspisK1.V7Tag73ExactFoldArmedQueryBatchProbabilityReady

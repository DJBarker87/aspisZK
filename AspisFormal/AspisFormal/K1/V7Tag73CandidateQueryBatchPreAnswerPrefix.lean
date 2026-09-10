import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
import AspisFormal.K1.V7Tag73CausalResidualCoordinatePrefix

/-!
# Candidate-directed prefix before the query-batch answer

The degree-sixteen K1.3 target is fixed before the nonzero query-batch
challenge is returned.  This module supplies the generic causal transport
lemma needed to make that statement source-exact: if two compiler tapes have
the same complete 542-coordinate context, then every literal root prefix that
has not yet consumed a query-batch sampler slot is replayed byte-for-byte.

The theorem reasons through the executable causal controller.  It does not
classify a SHA input retrospectively and it does not assume hash injectivity.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace AspisK1.V7Tag73CandidateQueryBatchPreAnswerPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Equal pre-query-batch coordinates replay every exact root prefix whose
named slots all belong to the established fold/alpha/final-work/q16 base.
In particular, the prefix may contain the query-batch domain absorb, which is
a residual coordinate, but no query-batch squeeze output or advance. -/
theorem exact_candidate_coordinates_force_pre_query_batch_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot)
    (prior later : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (baseExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        (exactCompilerFoldArmedCandidateQueryBatchRouter parameters
          transitionFuel foldTrial.val finalTrial.val target
          (exactPlainRomCursor configuration sample.1).erase) sample.2).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        (exactCompilerFoldArmedCandidateQueryBatchRouter parameters
          transitionFuel foldTrial.val finalTrial.val target
          (exactPlainRomCursor configuration sample.1).erase) right).1)
    (noQueryBatch :
      let controller := foldArmedCandidateQueryBatchController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel foldTrial.val finalTrial.val target
      let initial := exactFoldArmedCandidateQueryBatchInitialState input
      ∀ slot ∈ namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller initial
            prior),
        ∃ base : FoldAlphaFinalWorkQ16DigestSlot, slot = Sum.inl base) :
    ∃ rightRemaining,
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters right)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let controller := foldArmedCandidateQueryBatchController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel foldTrial.val finalTrial.val target
  let initial := exactFoldArmedCandidateQueryBatchInitialState input
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller prior initial) later
  have labelsExact :
      exactFoldArmedCandidateRootLabels input foldTrial finalTrial target =
        prefixLabels ++ suffixLabels := by
    unfold exactFoldArmedCandidateRootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  obtain ⟨prefixState, prefixTrace⟩ : ∃ prefixState,
      MachineLabeledTrace (controller.machine transitionFuel) initial
        prefixLabels prefixState := by
    have rootTrace := exact_fold_armed_candidate_root_labels_form_trace input
      foldTrial finalTrial target
    have splitTrace : MachineLabeledTrace (controller.machine transitionFuel)
        initial (prefixLabels ++ suffixLabels)
        (indexedStateAfterRecords transitionFuel controller
          (exactFixedRootRecords input.package.root) initial) := by
      simpa only [controller, initial, labelsExact] using rootTrace
    obtain ⟨middle, prefixPart, _suffixPart⟩ :=
      machine_labeled_trace_append_split prefixLabels suffixLabels splitTrace
    exact ⟨middle, prefixPart⟩
  have namedNodup : (namedTraceSlots prefixLabels).Nodup := by
    have full := exact_fold_armed_candidate_root_named_slots_nodup input
      foldTrial finalTrial target
    rw [labelsExact, named_trace_slots_append] at full
    exact List.Nodup.of_append_left full
  have residualEnough : residualTraceSteps prefixLabels ≤
      (exactCompilerTargetCaps parameters).length - 542 := by
    have full := exact_fold_armed_candidate_root_residual_enough input foldTrial
      finalTrial target programmedCover
    rw [labelsExact, residual_trace_steps_append] at full
    omega
  have leftPrefix : freshAnswerTapeToList
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (suffixLabels.map Prod.snd ++
          input.package.root.full.projection.rootPrefixes.verifier.remaining) := by
    rw [exact_fold_armed_candidate_root_labels_tape_prefix input foldTrial
      finalTrial target, labelsExact, List.map_append, List.append_assoc]
  have leftTraceExact : freshAnswerTapeToList
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)
          )).drop prefixLabels.length := by
    rw [leftPrefix]
    have prefixLength : (prefixLabels.map Prod.snd).length =
        prefixLabels.length := by simp
    rw [← prefixLength, List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  let router := exactCompilerFoldArmedCandidateQueryBatchRouter parameters
    transitionFuel foldTrial.val finalTrial.val target
      (exactPlainRomCursor configuration sample.1).erase
  let leftTape := foldAlphaQ16QueryBatchNamedSlotInputTape
    (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)
  let rightTape := foldAlphaQ16QueryBatchNamedSlotInputTape
    (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters right)
  have residualExact : (router.coordinateEquiv leftTape).2 =
      (router.coordinateEquiv rightTape).2 := by
    exact congrArg Prod.fst baseExact
  have baseNamedExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router sample.2).1.2 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        router right).1.2 := congrArg Prod.snd baseExact
  have namedExact : ∀ current : ↥(Finset.univ :
      Finset FoldAlphaFinalWorkQ16QueryBatchDigestSlot),
      current.1 ∈ namedTraceSlots prefixLabels →
        (router.coordinateEquiv leftTape).1 current =
          (router.coordinateEquiv rightTape).1 current := by
    intro current used
    obtain ⟨base, baseSlot⟩ := noQueryBatch current.1 used
    have currentExact : current =
        ⟨Sum.inl base, Finset.mem_univ _⟩ := Subtype.ext baseSlot
    subst current
    have baseFunctionExact := congrArg
      foldAlphaFinalWorkQ16DigestSlotFunctionEquiv.symm baseNamedExact
    have baseValueExact := congrFun baseFunctionExact base
    have baseCoordinateEq : ∀ tape : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length,
        (foldAlphaFinalWorkQ16DigestSlotFunctionEquiv.symm
          (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
            parameters router tape).1.2) base =
        (router.coordinateEquiv
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters tape))).1
          ⟨Sum.inl base, Finset.mem_univ _⟩ := by
      intro tape
      cases base with
      | none =>
          change
            (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
              parameters router tape).1.2.1 = _
          exact fold_alpha_q16_query_batch_fold_coordinate_eq_named_slot
            parameters router tape
      | some slot =>
          cases slot with
          | inl alpha =>
              change
                (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
                  parameters router tape).1.2.2.1 alpha = _
              simp only [exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates,
                exactCompilerFoldAlphaQ16QueryBatchInputTape,
                foldAlphaQ16QueryBatchNamedSlotInputTape,
                CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
                Equiv.prodCongr_apply,
                foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv,
                foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup,
                foldAlphaFinalWorkQ16DigestSlotFunctionEquiv,
                alphaFinalWorkQ16DigestSlotFunctionEquiv,
                finalWorkQ16DigestSlotFunctionEquiv, univSubtypeEquiv]
              rfl
          | inr finalSlot =>
              cases finalSlot with
              | none =>
                  change
                    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
                      parameters router tape).1.2.2.2.1 = _
                  exact
                    fold_alpha_q16_query_batch_final_work_coordinate_eq_named_slot
                      parameters router tape
              | some q16 =>
                  rcases q16 with ⟨counter, block⟩
                  change
                    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
                      parameters router tape).1.2.2.2.2 counter block = _
                  simp only [exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates,
                    exactCompilerFoldAlphaQ16QueryBatchInputTape,
                    foldAlphaQ16QueryBatchNamedSlotInputTape,
                    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
                    Equiv.prodCongr_apply,
                    foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv,
                    foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup,
                    foldAlphaFinalWorkQ16DigestSlotFunctionEquiv,
                    alphaFinalWorkQ16DigestSlotFunctionEquiv,
                    finalWorkQ16DigestSlotFunctionEquiv, univSubtypeEquiv]
                  rfl
    rw [baseCoordinateEq sample.2, baseCoordinateEq right] at baseValueExact
    change (router.coordinateEquiv leftTape).1
        ⟨Sum.inl base, Finset.mem_univ _⟩ =
      (router.coordinateEquiv rightTape).1
        ⟨Sum.inl base, Finset.mem_univ _⟩ at baseValueExact
    exact baseValueExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    trace_forces_right_prefix_of_used_coordinate_agreement prefixTrace
      namedNodup (fun slot _ => Finset.mem_univ slot) residualEnough leftTape
      rightTape leftTraceExact residualExact namedExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer := by
    exact indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  refine ⟨rightRemaining, ?_⟩
  rw [prefixAnswers] at rightPrefix
  exact rightPrefix

#print axioms exact_candidate_coordinates_force_pre_query_batch_prefix

end
end AspisK1.V7Tag73CandidateQueryBatchPreAnswerPrefix

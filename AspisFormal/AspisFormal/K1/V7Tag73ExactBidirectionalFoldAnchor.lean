import AspisFormal.K1.V7Tag73BidirectionalFoldOneFoldCoordinates
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaSourceAlignment

/-!
# Exact source anchor for the bidirectional fold/alpha controller

The selected fold-work input and its nonce-absorb boundary are both literal
first-creation records in the exact accepted root.  This file selects their
earlier record as the causal controller anchor, irrespective of which actor
first queried it and irrespective of the two possible chronological orders.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldAnchor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def selectedFoldWorkInput
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
    (fold : ExactAcceptedFoldTrial input) : ShaInput :=
  bytes fold.digest ++ [domGrind] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected

def selectedFoldBoundaryInput
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
    (fold : ExactAcceptedFoldTrial input) : ShaInput :=
  bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
    bytes (exactOperationalTape input).messages.foldGrinding.selected

/-- The first of the selected fold-work/boundary pair is the trial anchor.
Both actors and the complete strict root order remain proof-relevant. -/
def ExactAcceptedFoldPairLabeled
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
    (fold : ExactAcceptedFoldTrial input)
    (trial : ExactCompilerExposureTrial parameters) : Prop :=
  (∃ prior middle later boundaryActor,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh fold.actor (selectedFoldWorkInput input fold)
            fold.answer : UnifiedExposureRecord) ::
          middle ++
          (.machineFresh boundaryActor (selectedFoldBoundaryInput input fold)
            fold.boundaryAnswer : UnifiedExposureRecord) :: later ∧
      trial.val = prior.length) ∨
  (∃ prior middle later boundaryActor,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh boundaryActor (selectedFoldBoundaryInput input fold)
            fold.boundaryAnswer : UnifiedExposureRecord) ::
          middle ++
          (.machineFresh fold.actor (selectedFoldWorkInput input fold)
            fold.answer : UnifiedExposureRecord) :: later ∧
      trial.val = prior.length)

theorem exact_accepted_fold_pair_labeled_exists
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
    (fold : ExactAcceptedFoldTrial input) :
    ∃ trial : ExactCompilerExposureTrial parameters,
      ExactAcceptedFoldPairLabeled input fold trial := by
  obtain ⟨boundaryActor, before | after⟩ :=
    exact_accepted_fold_boundary_record_before_or_after input fold
  · obtain ⟨prior, middle, priorExact⟩ := (List.mem_iff_append).mp before
    have priorLtRoot : prior.length <
        (exactFixedRootRecords input.package.root).length := by
      rw [fold.rootDecomposition, priorExact]
      simp
    have priorLtCap : prior.length < unifiedFull256ExposureCap parameters := by
      rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
      apply priorLtRoot.trans_le
      rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
      unfold exactFixedOperationalStateMapTrace
      simp
    let trial : ExactCompilerExposureTrial parameters :=
      ⟨prior.length, priorLtCap⟩
    refine ⟨trial, Or.inr ⟨prior, middle, fold.later, boundaryActor, ?_, rfl⟩⟩
    rw [fold.rootDecomposition, priorExact]
    simp only [selectedFoldWorkInput, selectedFoldBoundaryInput,
      List.cons_append, List.append_assoc]
  · obtain ⟨middle, later, laterExact⟩ := (List.mem_iff_append).mp after
    refine ⟨fold.trial, Or.inl
      ⟨fold.prior, middle, later, boundaryActor, ?_, fold.trialExact⟩⟩
    rw [fold.rootDecomposition, laterExact]
    simp only [selectedFoldWorkInput, selectedFoldBoundaryInput,
      List.cons_append, List.append_assoc]

noncomputable def exactAcceptedFoldPairTrial
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
    (fold : ExactAcceptedFoldTrial input) :
    ExactCompilerExposureTrial parameters :=
  Classical.choose (exact_accepted_fold_pair_labeled_exists input fold)

theorem exactAcceptedFoldPairTrial_labeled
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
    (fold : ExactAcceptedFoldTrial input) :
    ExactAcceptedFoldPairLabeled input fold
      (exactAcceptedFoldPairTrial input fold) :=
  Classical.choose_spec (exact_accepted_fold_pair_labeled_exists input fold)

/-- The exact accepted root is aligned with the new five-coordinate
controller for the selected pair anchor. -/
theorem exact_root_records_aligned_for_bidirectional_fold_controller
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
    (anchorTrial : ExactCompilerExposureTrial parameters) :
    IndexedRecordsAligned transitionFuel
      (bidirectionalFoldAlphaController transitionFuel anchorTrial.val)
      (bidirectionalFoldAlphaInitialState
        (exactPlainRomCursor configuration sample.1).erase)
      (exactFixedRootRecords input.package.root) := by
  let controller := bidirectionalFoldAlphaController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel anchorTrial.val
  let initial := bidirectionalFoldAlphaInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let rootTape := operationalTapeCoordinates
    (globalFull256OracleCallCap parameters) 1
    (unifiedFull256ExposureCap parameters)
    (exactCompilerOperationalIndexedTape parameters sample.2)
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase rootTape =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa [rootTape, exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  have fullAligned := indexed_records_aligned_of_trace transitionFuel
    controller initial rootTape
      (runExactPlainRom transitionFuel configuration sample).trace traceExact
  have fullSplit :
      (runExactPlainRom transitionFuel configuration sample).trace =
        [] ++ exactFixedRootRecords input.package.root ++
          (exactFixedComputedClientTailRun transitionFuel configuration sample
            input.package.root).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    rfl
  have rootAligned := indexed_records_aligned_segment transitionFuel controller
    initial (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil, controller, initial] using
    rootAligned

end


#print axioms ExactAcceptedFoldPairLabeled
#print axioms exact_accepted_fold_pair_labeled_exists
#print axioms exactAcceptedFoldPairTrial_labeled
#print axioms exact_root_records_aligned_for_bidirectional_fold_controller

end AspisK1.V7Tag73ExactBidirectionalFoldAnchor

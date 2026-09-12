import AspisFormal.K1.V7Tag73ConcreteRestorationMustReachForkCap
import AspisFormal.K1.V7Tag73ExactRestoredGammaActualTrace
import AspisFormal.K1.V7Tag73GammaRestoredK14PrefixCapacity

/-!
# Fork-capped occurrence of the restored gamma fork

The one-round production sweep reaches the canonical root-gamma request after
at most two fork coordinates per earlier request.  This module transports that
local scheduler certificate into the literal completed compiler trace, while
showing that the root-machine prefix contributes no fork coordinates.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredGammaActualTraceForkCap

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRestorationMustReachForkCap
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomOperationalCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactRestoredGammaActualTrace
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73GammaRestoredK14PrefixCapacity
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73SchedulerNativeMustReach
open AspisK1.V7Tag73SchedulerNativeMustReachForkCap
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73TotalizedMachineReflection

noncomputable section

/-- The exact one-round production trace contains the canonical typed gamma
fork, and its entire chronological prefix consumes no more than the reserved
fork-coordinate budget for that transition. -/
theorem exact_one_round_full_trace_contains_typed_gamma_fork_with_cap
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    (withinForkCap : 1 * 1513 ≤ parameters.forkRequestCap)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base 1 extractor withinForkCap))
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel
      (exactRootSweepWitnessConfiguration base 1 extractor withinForkCap)
      projection fixedInstance sample) :
    ∃ (prior later : List UnifiedExposureRecord)
        (selected : UnifiedExposureRecord)
        (targetCursor : SchedulerNativeCursor
          (globalFull256OracleCallCap parameters)
          (ConcreteRestorationClientRun Statement Tag73K12ParsedProof Payload
            (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
              Payload Witness)))
        (answer : Digest256)
        (request : ConcreteRestorationRequest),
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base 1 extractor withinForkCap)
          sample).trace = prior ++ selected :: later ∧
      forkCoordinateCount prior ≤
        exactGammaRestoredPrefixForkCap request.verifierTransitionIndex ∧
      typedRestoredGammaForkStartsHere
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration
          targetCursor.erase = true ∧
      IsTypedRestoredChallengeForkStartForRequest
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (.challenge .gamma) request
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration
          targetCursor.erase ∧
      Nonempty (ExactRootGammaRestorationRequest input request) ∧
      request = exactOperationalRootGammaRestorationRequest input ∧
      selected = schedulerNativeRequestRecord
        (seekSchedulerNativeExposure transitionFuel targetCursor) answer := by
  let configuration :=
    exactRootSweepWitnessConfiguration base 1 extractor withinForkCap
  let request := exactOperationalRootGammaRestorationRequest input
  let requestTyped : ExactRootGammaRestorationRequest input request :=
    exact_operational_root_gamma_restoration_request_is_typed input
  have requestShape :
      ({ nodeId := 0,
          verifierTransitionIndex := request.verifierTransitionIndex } :
        ConcreteRestorationRequest) = request := by
    cases requestExact : request with
    | mk nodeId verifierTransitionIndex =>
        have rootNode := requestTyped.rootNode
        rw [requestExact] at rootNode
        simp only at rootNode ⊢
        subst nodeId
        rfl
  have transitionPositive : 0 < transitionFuel := by
    have reserve := adequate.schedulerTransitionFuel
    unfold exactCompilerSufficientTransitionFuel at reserve
    omega
  have runs : RootProjectedTotalizedRuns configuration.machine sample.1
      input.package.root.fixedRoot.base.runtime :=
    completed_exact_plain_rom_root_gives_projected_totalized_runs
      transitionFuel transitionPositive configuration sample
      input.package.root.fixedRoot.base.runtime
      input.package.root.fixedRoot.base.clientRun
      input.package.root.fixedRoot.base.rootCompleted
  have reaches :=
    production_one_round_configuration_must_reach_gamma_with_fork_cap
      base extractor withinForkCap adequate sample.1
      input.package.root.fixedRoot.base.runtime runs
      request.verifierTransitionIndex requestTyped.transitionWithin
      requestTyped.transition requestTyped.transitionExact requestTyped.reply
      requestTyped.eventExact
  have reachesExact : SchedulerNativeCursorMustReachWithForkCap
      (fun cursor =>
        IsTypedRestoredChallengeForkStartForRequest
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (.challenge .gamma) request
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration cursor.erase)
      (2 * request.verifierTransitionIndex)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start sample.1 base.machine.observation)
        base.machine.environment input.package.root.fixedRoot.base.runtime.node
        base.restorationConfiguration 1513
        (deployedRootSweepClient 1 extractor)) := by
    simpa only [requestShape] using reaches
  have clientCompleted :
      (runSchedulerNativeListRunFrom transitionFuel
        (exactFixedClientContinuationFuel transitionFuel input.package.root)
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment input.package.root.fixedRoot.base.runtime.node
          base.restorationConfiguration 1513
          (deployedRootSweepClient 1 extractor))
        input.package.root.full.projection.rootPrefixes.verifier.remaining).terminal =
          .returned input.package.root.full.clientRun := by
    rw [run_scheduler_native_list_run_terminal]
    exact input.package.factorization.computedClientListTerminalExact
  have continuationPositive :
      0 < exactFixedClientContinuationFuel transitionFuel input.package.root :=
    returned_list_terminal_implies_current_positive transitionFuel
      transitionPositive
      (exactFixedClientContinuationFuel transitionFuel input.package.root)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start sample.1 base.machine.observation)
        base.machine.environment input.package.root.fixedRoot.base.runtime.node
        base.restorationConfiguration 1513
        (deployedRootSweepClient 1 extractor))
      input.package.root.full.projection.rootPrefixes.verifier.remaining
      input.package.root.full.clientRun (by
        exact input.package.factorization.computedClientListTerminalExact)
  obtain ⟨tailPrior, tailLater, selected, targetCursor, answer, tailExact,
      tailForkBound, exactRequest, selectedExact⟩ :=
    returned_run_of_fork_capped_must_reach_contains_target
      (fun cursor =>
        IsTypedRestoredChallengeForkStartForRequest
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (.challenge .gamma) request
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration cursor.erase)
      transitionFuel transitionPositive
      (fun cursor exactRequest =>
        native_cursor_with_typed_gamma_marker_is_fork_pair
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration cursor (by
            unfold typedRestoredGammaForkStartsHere
            rw [typed_restored_challenge_fork_starts_here_iff]
            exact typed_restored_challenge_for_request_implies_marker
              (.challenge .gamma) request
              (base.machine.blackBox.start sample.1 base.machine.observation)
              base.machine.environment base.restorationConfiguration
              cursor.erase exactRequest))
      (2 * request.verifierTransitionIndex)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start sample.1 base.machine.observation)
        base.machine.environment input.package.root.fixedRoot.base.runtime.node
        base.restorationConfiguration 1513
        (deployedRootSweepClient 1 extractor))
      reachesExact
      (exactFixedClientContinuationFuel transitionFuel input.package.root)
      continuationPositive
      input.package.root.full.projection.rootPrefixes.verifier.remaining
      input.package.root.full.clientRun clientCompleted
  have marked : typedRestoredGammaForkStartsHere
      (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
        Payload Witness)
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration
      targetCursor.erase = true := by
    unfold typedRestoredGammaForkStartsHere
    rw [typed_restored_challenge_fork_starts_here_iff]
    exact typed_restored_challenge_for_request_implies_marker
      (.challenge .gamma) request
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration targetCursor.erase
      exactRequest
  let rootRecords := exactFixedRootRecords input.package.root
  let clientTail := exactFixedComputedClientTailRun transitionFuel configuration
    sample input.package.root
  have rootForkZero : forkCoordinateCount rootRecords = 0 := by
    unfold rootRecords exactFixedRootRecords fullProjectedRootRecords
    simp [forkCoordinateCount]
  have fullTraceFactor :
      (runExactPlainRom transitionFuel configuration sample).trace =
        rootRecords ++ clientTail.trace := by
    unfold runExactPlainRom
    rw [run_scheduler_native_eq_list_run]
    have exact := congrArg SchedulerNativeRun.trace
      input.package.factorization.fullRunExact
    simpa only [SchedulerNativeRun.trace, runSchedulerNativeListRun,
      configuration, rootRecords, clientTail] using exact
  refine ⟨rootRecords ++ tailPrior, tailLater, selected, targetCursor, answer,
    request, ?_, ?_, marked, ?_, ⟨requestTyped⟩, rfl, selectedExact⟩
  · rw [fullTraceFactor]
    change rootRecords ++
        (runSchedulerNativeListRunFrom transitionFuel
          (exactFixedClientContinuationFuel transitionFuel input.package.root)
          (startConcreteRestorationClientFromRoot
            (globalOracleCalls := globalFull256OracleCallCap parameters)
            (base.machine.blackBox.start sample.1 base.machine.observation)
            base.machine.environment
            input.package.root.fixedRoot.base.runtime.node
            base.restorationConfiguration 1513
            (deployedRootSweepClient 1 extractor))
          input.package.root.full.projection.rootPrefixes.verifier.remaining).trace =
        (rootRecords ++ tailPrior) ++ selected :: tailLater
    rw [tailExact, List.append_assoc]
  · rw [fork_coordinate_count_append, rootForkZero, Nat.zero_add]
    unfold exactGammaRestoredPrefixForkCap
    omega
  · simpa only [request] using exactRequest

#print axioms exact_one_round_full_trace_contains_typed_gamma_fork_with_cap

end
end AspisK1.V7Tag73ExactRestoredGammaActualTraceForkCap

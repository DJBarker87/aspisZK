import AspisFormal.K1.V7Tag73ConcreteRootSweepMustReachGamma
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.K1.V7Tag73ExactFixedFullRunFactorization
import AspisFormal.K1.V7Tag73GammaRestoredK14Scope

/-!
# Actual completed-run occurrence of the restored gamma fork

The production root sweep statically reaches the typed block-zero gamma
dispatcher on every continuation.  This module applies that certificate to
the literal completed client tail retained by `ExactK12OperationalInput` and
then prepends the exact root records.  The result is an occurrence in the
real full Tag-73 trace, not a selected synthetic replay branch.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredGammaActualTrace

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ConcreteRootSweepMustReachGamma
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomOperationalCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73SchedulerNativeMustReach
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment

noncomputable section

/-- Native and result-erased cursors emit the same literal record at their
next exposure. -/
theorem scheduler_native_record_eq_unified_record_at_answer
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answer : Digest256) :
    schedulerNativeRequestRecord
        (seekSchedulerNativeExposure transitionFuel cursor) answer =
      unifiedRecordAtAnswer transitionFuel cursor.erase answer := by
  unfold unifiedRecordAtAnswer
  rw [← erase_seek_scheduler_native_exposure transitionFuel cursor]
  generalize requestExact : seekSchedulerNativeExposure transitionFuel cursor =
    request
  cases request <;> rfl

/-- The exact full production trace contains the fork-output record of the
typed restored gamma dispatcher.  Its answer is the literal master-tape
answer consumed by that occurrence. -/
theorem exact_root_sweep_full_trace_contains_typed_gamma_fork
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (rounds : Nat)
    (roundsPositive : 0 < rounds)
    (extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor
          withinForkCap))
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
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
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample).trace =
        prior ++ selected :: later ∧
      typedRestoredGammaForkStartsHere
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration
          targetCursor.erase = true ∧
      IsTypedRestoredChallengeForkStartForRequest
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (.challenge .gamma)
          request
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration
          targetCursor.erase ∧
      Nonempty (ExactRootGammaRestorationRequest input request) ∧
      selected = schedulerNativeRequestRecord
        (seekSchedulerNativeExposure transitionFuel targetCursor) answer := by
  let configuration :=
    exactRootSweepWitnessConfiguration base rounds extractor withinForkCap
  obtain ⟨transitionIndex, transition, reply, transitionExact,
      transitionWithin, eventExact, reaches⟩ :=
    production_clean_root_must_reach_gamma base rounds roundsPositive
      extractor withinForkCap adequate projection sample
        input.package.root.fixedRoot.base
  have transitionPositive : 0 < transitionFuel := by
    have reserve := adequate.schedulerTransitionFuel
    unfold exactCompilerSufficientTransitionFuel at reserve
    omega
  have clientCompleted :
      (runSchedulerNativeListRunFrom transitionFuel
        (exactFixedClientContinuationFuel transitionFuel input.package.root)
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment input.package.root.fixedRoot.base.runtime.node
          base.restorationConfiguration (rounds * 1513)
          (deployedRootSweepClient rounds extractor))
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
        base.restorationConfiguration (rounds * 1513)
        (deployedRootSweepClient rounds extractor))
      input.package.root.full.projection.rootPrefixes.verifier.remaining
      input.package.root.full.clientRun (by
        exact input.package.factorization.computedClientListTerminalExact)
  obtain ⟨tailPrior, tailLater, selected, targetCursor, answer, tailExact,
      exactRequest, selectedExact⟩ :=
    returned_run_of_must_reach_contains_target_fork
      (fun cursor =>
        IsTypedRestoredChallengeForkStartForRequest
          (Result := ExactPlainRomWitnessExtractor Statement
            Tag73K12ParsedProof Payload Witness)
          (.challenge .gamma)
          { nodeId := 0, verifierTransitionIndex := transitionIndex }
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration
          cursor.erase)
      transitionFuel transitionPositive
      (fun cursor exactRequest =>
        native_cursor_with_typed_gamma_marker_is_fork_pair
          (base.machine.blackBox.start sample.1 base.machine.observation)
          base.machine.environment base.restorationConfiguration cursor (by
            unfold typedRestoredGammaForkStartsHere
            rw [typed_restored_challenge_fork_starts_here_iff]
            exact typed_restored_challenge_for_request_implies_marker
              (.challenge .gamma)
              { nodeId := 0, verifierTransitionIndex := transitionIndex }
              (base.machine.blackBox.start sample.1 base.machine.observation)
              base.machine.environment base.restorationConfiguration
              cursor.erase exactRequest))
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start sample.1 base.machine.observation)
        base.machine.environment input.package.root.fixedRoot.base.runtime.node
        base.restorationConfiguration (rounds * 1513)
        (deployedRootSweepClient rounds extractor))
      reaches
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
      (.challenge .gamma)
      { nodeId := 0, verifierTransitionIndex := transitionIndex }
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration targetCursor.erase
      exactRequest
  let request : ConcreteRestorationRequest :=
    { nodeId := 0, verifierTransitionIndex := transitionIndex }
  let requestTyped : ExactRootGammaRestorationRequest input request :=
    { rootNode := rfl
      transition := transition
      reply := reply
      transitionExact := transitionExact
      eventExact := eventExact }
  let rootRecords := exactFixedRootRecords input.package.root
  let clientTail := exactFixedComputedClientTailRun transitionFuel configuration
    sample input.package.root
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
    request, ?_, marked, ?_, ⟨requestTyped⟩, selectedExact⟩
  · rw [fullTraceFactor]
    change rootRecords ++
        (runSchedulerNativeListRunFrom transitionFuel
          (exactFixedClientContinuationFuel transitionFuel input.package.root)
          (startConcreteRestorationClientFromRoot
            (globalOracleCalls := globalFull256OracleCallCap parameters)
            (base.machine.blackBox.start sample.1 base.machine.observation)
            base.machine.environment
            input.package.root.fixedRoot.base.runtime.node
            base.restorationConfiguration (rounds * 1513)
            (deployedRootSweepClient rounds extractor))
          input.package.root.full.projection.rootPrefixes.verifier.remaining).trace =
        (rootRecords ++ tailPrior) ++ selected :: tailLater
    rw [tailExact, List.append_assoc]
  · simpa only [request] using exactRequest

#print axioms exact_root_sweep_full_trace_contains_typed_gamma_fork
#print axioms scheduler_native_record_eq_unified_record_at_answer

end
end AspisK1.V7Tag73ExactRestoredGammaActualTrace

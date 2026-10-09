import FSV8AlphaRootLabeledTraceConstructor
import FSV8ReturnedRootFreshTracePrefix

/-!
# Residual capacity for an actual-root alpha prefix

This leaf discharges the finite residual-capacity side for a chronological
machine-fresh prefix of one returned exact root.  The root-trace decomposition
is constructed from `SuccessfulRootMachinePrefixes`; it is not supplied by the
caller.  The only resource premise retained is the source-facing full-machine
fresh-coordinate cap.  That premise is deliberately stated on the actual
returned verifier state so the remaining configuration-to-cap bridge is
visible rather than hidden in an unrelated list-length assumption.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8ActualRootAlphaPrefixResidualCapacity

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73VerifierOracleStability
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorOperationalAlphaScheduler
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8AlphaRootLabeledTraceConstructor
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes
open FSV8ReturnedRootFreshTracePrefix

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- A chronological intermediate verifier state selects a literal prefix of
the returned verifier's projected fresh-query list.  The selected list is
computed from the two actual histories; no list split is supplied. -/
theorem intermediate_history_selects_returned_verifier_fresh_prefix
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
      fallback runtime)
    (intermediate : OracleState)
    (entryPrefix : prefixes.adversary.finalState.history <+:
      intermediate.history)
    (finalPrefix : intermediate.history <+:
      prefixes.verifier.finalState.history) :
    ∃ verifierLater,
      prefixes.verifier.freshQueries =
        freshQueryEnumeration
          (historySince prefixes.adversary.finalState intermediate) ++
            verifierLater := by
  rcases entryPrefix with ⟨between, intermediateExact⟩
  rcases finalPrefix with ⟨after, finalExact⟩
  have enumerationExact :=
    projected_fresh_returned_trace_fresh_query_enumeration_exact
      configuration.verifierLimits .verifier (stagedBudget n m)
      prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        prefixes.adversary.result configuration.initialDigest))
      prefixes.verifier.freshQueries prefixes.verifier.result
      prefixes.verifier.finalState prefixes.verifier.steps
      prefixes.verifier.trace
  refine ⟨freshQueryEnumeration after, ?_⟩
  rw [← enumerationExact]
  unfold historySince
  rw [← finalExact, ← intermediateExact]
  simp [fresh_query_enumeration_append]

/-- A verifier fresh-query prefix selected from the same returned root has an
actual root-trace decomposition and fits the alpha router's residual, provided
the returned source execution satisfies its concrete machine-fresh cap.  The
four-fork reserve is exactly the eight output/advance coordinates reserved by
the alpha router. -/
theorem returned_root_verifier_prefix_residual_enough
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (continuationPositive : 1 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration sample.1 sample.2
      fallback runtime)
    (verifierPrior verifierLater : List (ShaInput × Block))
    (verifierSplit : prefixes.verifier.freshQueries =
      verifierPrior ++ verifierLater)
    (sourceFreshCap : prefixes.verifier.finalState.freshCalls ≤
      full256MachineFreshCap parameters)
    (routerReserve : 4 ≤ parameters.forkRequestCap) :
    let records :=
      projectedMachineFreshRecords .adversary prefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier verifierPrior
    (∃ later,
      (runExactRoot parameters configuration transitionFuel sample).trace =
        records ++ later) ∧
      residualTraceSteps
          (alpha0RootLabeledRecords configuration transitionFuel sample.1
            records) ≤
        relationAlphaRouterResidual parameters := by
  let records :=
    projectedMachineFreshRecords .adversary prefixes.adversary.freshQueries ++
      projectedMachineFreshRecords .verifier verifierPrior
  have rootPrefix := returned_exact_root_trace_has_fresh_machine_prefix
    parameters configuration transitionFuel positive continuationPositive
    sample fallback runtime prefixes
  rcases rootPrefix with ⟨rootLater, rootExact⟩
  refine ⟨?_, ?_⟩
  · refine ⟨projectedMachineFreshRecords .verifier verifierLater ++ rootLater,
      ?_⟩
    rw [verifierSplit] at rootExact
    simpa only [records, projected_machine_fresh_records_append,
      List.append_assoc] using rootExact.symm
  · have residualLeLabels :
        residualTraceSteps
            (alpha0RootLabeledRecords configuration transitionFuel sample.1
              records) ≤
          (alpha0RootLabeledRecords configuration transitionFuel sample.1
            records).length := by
      have split := labeled_trace_length_split
        (alpha0RootLabeledRecords configuration transitionFuel sample.1 records)
      omega
    have labelsLength :
        (alpha0RootLabeledRecords configuration transitionFuel sample.1
          records).length = records.length := by
      have answers := congrArg List.length
        (alpha0_root_labeled_records_answers configuration transitionFuel
          sample.1 records)
      simpa using answers
    have adversaryFresh :=
      projected_fresh_returned_trace_fresh_calls_exact
        configuration.adversaryLimits .adversary configuration.adversaryFuel
        emptyOracle
        (configuration.blackBox.start sample.1 configuration.observation)
        prefixes.adversary.freshQueries prefixes.adversary.result
        prefixes.adversary.finalState prefixes.adversary.steps
        prefixes.adversary.trace
    have verifierFresh :=
      projected_fresh_returned_trace_fresh_calls_exact
        configuration.verifierLimits .verifier (stagedBudget n m)
        prefixes.adversary.finalState
        (compileScript (wholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          prefixes.adversary.result configuration.initialDigest))
        prefixes.verifier.freshQueries prefixes.verifier.result
        prefixes.verifier.finalState prefixes.verifier.steps
        prefixes.verifier.trace
    have priorLe : verifierPrior.length ≤
        prefixes.verifier.freshQueries.length := by
      rw [verifierSplit, List.length_append]
      omega
    have recordsLeFinal : records.length ≤
        prefixes.verifier.finalState.freshCalls := by
      simp only [records, List.length_append]
      have adversaryLength :
          prefixes.adversary.finalState.freshCalls =
            prefixes.adversary.freshQueries.length := by
        simpa [emptyOracle] using adversaryFresh
      rw [verifierFresh, adversaryLength]
      have projectedLength (actor : QueryActor) :
          ∀ queries : List (ShaInput × Block),
            (projectedMachineFreshRecords actor queries).length =
              queries.length := by
        intro queries
        induction queries with
        | nil => rfl
        | cons query queries ih =>
            rcases query with ⟨input, answer⟩
            simp [projectedMachineFreshRecords, ih]
      rw [projectedLength, projectedLength]
      omega
    have machineCapLeResidual : full256MachineFreshCap parameters ≤
        relationAlphaRouterResidual parameters := by
      unfold relationAlphaRouterResidual
      rw [exact_compiler_target_caps_length]
      unfold unifiedFull256ExposureCap sameTapeStartCap
      rw [relation_alpha_duplex_slot_card]
      omega
    exact residualLeLabels.trans
      (labelsLength.le.trans
        (recordsLeFinal.trans (sourceFreshCap.trans machineCapLeResidual)))

#print axioms returned_root_verifier_prefix_residual_enough
#print axioms intermediate_history_selects_returned_verifier_fresh_prefix

end
end AspisV8Completion.FSV8ActualRootAlphaPrefixResidualCapacity

import FSV8ExactRootSuccessfulPrefixes
import FSV8FreshTapeBudget
import FSV8BeforeAlphaMarkerFactorization
import AspisFormal.K1.V7Tag73SchedulerCompletionCore

/-!
# Source-facing fresh-coordinate cap for an exact V8 root

The generic V8 `Configuration` does not relate its adversary fuel or
statically indexed work scripts to the compiler's machine-fresh cap.  The
alpha router only needs the prefix through the accepted alpha pair, not the
later verifier suffix.  This leaf proves the exact allocation arithmetic for
that prefix: `1403+n+m` verifier coordinates fit the existing `1511` root
allowance when `n+m≤108`, alongside the adversary Q1 cap.

The selected producers of those source facts remain explicit.  The older
V7-specific `1511` is not asserted to bound the whole V8 `stagedBudget`.
Whole-run fuel bounds are retained below only as stronger generic helpers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8ActualRootSourceFreshCap

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerCompletionCore
open AspisK1.V7Tag73SchedulerTraceFactorization
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8FreshTapeBudget
open FSV8BeforeAlphaMarkerFactorization
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes

noncomputable section

abbrev Block := FSBoundedTranscript.Block

private theorem projected_machine_fresh_records_length
    (actor : QueryActor) : ∀ queries : List (ShaInput × Block),
    (projectedMachineFreshRecords actor queries).length = queries.length := by
  intro queries
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, ih]

/-- The chronological verifier prefix through the accepted alpha pair has
source budget

`sourceThenGammaBudget n m + beforeAlphaMarkerBudget + 9 = 1403 + n + m`.

Once its source-produced list-length bound is available, the selected
`n+m≤108` profile and adversary Q1 cap place the corresponding root records
inside the original `q1+1511` root allocation.  This is the prefix-specific
endpoint needed by alpha routing; it does not bound the later verifier suffix.
-/
theorem actual_alpha_prefix_records_le_full256MachineFreshCap
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
      fallback runtime)
    (verifierPrior : List (ShaInput × Block))
    (priorSourceBound : verifierPrior.length ≤
      sourceThenGammaBudget n m + beforeAlphaMarkerBudget + 9)
    (adversaryFuelBound : configuration.adversaryFuel ≤
      parameters.q1ShaCallCap)
    (workBudgetBound : n + m ≤ 108) :
    (projectedMachineFreshRecords .adversary
        prefixes.adversary.freshQueries ++
      projectedMachineFreshRecords .verifier verifierPrior).length ≤
        full256MachineFreshCap parameters := by
  have adversaryLength :=
    projected_machine_prefix_fresh_length_le_fuel
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      emptyOracle
      (configuration.blackBox.start hidden configuration.observation)
      (freshAnswerTapeToList finiteTape) prefixes.adversary
  rw [List.length_append, projected_machine_fresh_records_length,
    projected_machine_fresh_records_length]
  unfold sourceThenGammaBudget at priorSourceBound
  unfold beforeAlphaMarkerBudget at priorSourceBound
  unfold full256MachineFreshCap deployedFull256VerifierCallCap
  omega

/-- The literal adversary and verifier prefixes cannot consume more fresh
answers than their two machine fuels.  This is independent of cache behavior:
cache hits only reduce the fresh count. -/
theorem returned_root_final_fresh_le_source_budgets
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
      fallback runtime) :
    prefixes.verifier.finalState.freshCalls ≤
      configuration.adversaryFuel + stagedBudget n m := by
  have adversaryExact :=
    projected_fresh_returned_trace_fresh_calls_exact
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      emptyOracle
      (configuration.blackBox.start hidden configuration.observation)
      prefixes.adversary.freshQueries prefixes.adversary.result
      prefixes.adversary.finalState prefixes.adversary.steps
      prefixes.adversary.trace
  have verifierExact :=
    projected_fresh_returned_trace_fresh_calls_exact
      configuration.verifierLimits .verifier (stagedBudget n m)
      prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        prefixes.adversary.result configuration.initialDigest))
      prefixes.verifier.freshQueries prefixes.verifier.result
      prefixes.verifier.finalState prefixes.verifier.steps
      prefixes.verifier.trace
  have adversaryLength :=
    projected_machine_prefix_fresh_length_le_fuel
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      emptyOracle
      (configuration.blackBox.start hidden configuration.observation)
      (freshAnswerTapeToList finiteTape) prefixes.adversary
  have verifierLength :=
    projected_machine_prefix_fresh_length_le_fuel
      configuration.verifierLimits .verifier (stagedBudget n m)
      prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        prefixes.adversary.result configuration.initialDigest))
      prefixes.adversary.remaining prefixes.verifier
  simp only [emptyOracle, Nat.zero_add] at adversaryExact
  omega

/-- A source-level static allocation is sufficient to produce the outcome
cap consumed by the alpha residual-capacity theorem. -/
theorem returned_root_final_fresh_le_full256MachineFreshCap
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
      fallback runtime)
    (sourceAllocation : configuration.adversaryFuel + stagedBudget n m ≤
      full256MachineFreshCap parameters) :
    prefixes.verifier.finalState.freshCalls ≤
      full256MachineFreshCap parameters :=
  (returned_root_final_fresh_le_source_budgets configuration hidden finiteTape
    fallback runtime prefixes).trans sourceAllocation

#print axioms returned_root_final_fresh_le_source_budgets
#print axioms returned_root_final_fresh_le_full256MachineFreshCap
#print axioms actual_alpha_prefix_records_le_full256MachineFreshCap

end
end AspisV8Completion.FSV8ActualRootSourceFreshCap

import AspisFormal.K1.V7Tag73ConcreteRootSweepClient
import AspisFormal.K1.V7Tag73ConcreteRestorationTraceInduction
import AspisFormal.K1.V7Tag73RootSqueezeForkEmission

/-!
# Root-sweep bridge to a typed query-batch fork

The raw SHA input alone does not identify a Tag-73 challenge role: an
adversary may expose the same coordinate before the verifier reaches it.  The
state-restoration preparer has a stronger source of information.  It selects
one literal verifier transition before either uniform fork coin is exposed,
and that transition retains the exact `SqueezeOwner` and sampler block.

This module specializes the generic root-squeeze dispatcher theorem to the
query-batch challenge and joins it to the deployed exhaustive root sweep.
The result is deterministic.  It neither assumes freshness nor assigns a
probability to a fork response.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RootQueryBatchForkBridge

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRestorationTraceInduction
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73RootSqueezeForkEmission
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

universe u

/-- A selected root query-batch transition emits a fork whose typed owner and
block are fixed before either fork answer is exposed. -/
theorem literal_root_query_batch_dispatch_emits_typed_fork
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (totalLimitMono : machine.adversaryLimits.totalCalls ≤
      configuration.oracleLimits.totalCalls)
    (freshLimitMono : machine.adversaryLimits.freshCalls ≤
      configuration.oracleLimits.freshCalls)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (block : Nat) (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) block) reply)
    (environment : FutureFreeEnvironment)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    ∃ (prepared : PreparedConcreteRestoration Statement Proof Payload)
        (role : PreparedRestorationPairRole),
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      prepared.transition = transition ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.owner = .challenge .queryBatch ∧
      role.block = block ∧
      role.outputInput =
        bytes transition.before.core.digest ++ [domSqueeze] ∧
      role.advanceInput =
        bytes transition.before.core.digest ++ [domAdvance] ∧
      (configuration.oracleLimits.totalCalls ≤ globalOracleCalls →
        prepared.programmingBase.history.length + 2 ≤ globalOracleCalls →
        schedulerNativePairForkHeader?
            (dispatchOneConcreteRestoration
              (machine.blackBox.start hidden machine.observation) environment
              configuration accumulator
              { nodeId := 0, verifierTransitionIndex := transitionIndex }
              resume) =
          some (preparedForkHeader configuration prepared)) := by
  let outputInput := bytes transition.before.core.digest ++ [domSqueeze]
  let advanceInput := bytes transition.before.core.digest ++ [domAdvance]
  have pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput) := by
    rw [squeezePairInputsOfTransition, eventExact]
  obtain ⟨prepared, role, ready, coherent, projected, _inputs,
      outputExact, advanceExact, emits⟩ :=
    literal_root_squeeze_dispatch_emits_typed_fork machine hidden runtime runs
      configuration totalLimitMono freshLimitMono transitionIndex transition
      transitionExact outputInput advanceInput pairExact environment accumulator
      rootStored resume
  have requestExact := ready_preparation_request_exact
    (machine.blackBox.start hidden machine.observation) configuration
    accumulator { nodeId := 0, verifierTransitionIndex := transitionIndex }
    prepared ready
  have selection := prepare_concrete_restoration_ready_selection_exact
    (machine.blackBox.start hidden machine.observation) configuration
    accumulator { nodeId := 0, verifierTransitionIndex := transitionIndex }
    prepared ready
  have parentLookup : accumulator.node? 0 = some prepared.parentNode := by
    simpa [requestExact] using selection.1
  have parentExact : prepared.parentNode = runtime.node := by
    rw [rootStored] at parentLookup
    exact Option.some.inj parentLookup.symm
  have selectedTransition : verifierTransitionAt? runtime.node transitionIndex =
      some prepared.transition := by
    simpa [requestExact, parentExact] using selection.2.1
  have preparedTransitionExact : prepared.transition = transition := by
    rw [transitionExact] at selectedTransition
    exact Option.some.inj selectedTransition.symm
  have roleExact : role =
      { owner := .challenge .queryBatch
        block := block
        outputInput := prepared.outputInput
        advanceInput := prepared.advanceInput } := by
    unfold preparedRestorationPairRole? at projected
    rw [preparedTransitionExact, eventExact] at projected
    exact Option.some.inj projected.symm
  subst role
  refine ⟨prepared,
    { owner := .challenge .queryBatch
      block := block
      outputInput := prepared.outputInput
      advanceInput := prepared.advanceInput },
    ready, coherent, preparedTransitionExact, projected, rfl, rfl, ?_, ?_,
    emits⟩
  · simpa [preparedTransitionExact] using outputExact
  · simpa [preparedTransitionExact] using advanceExact

/-- Every adaptive reply path through a positive deployed root sweep contains
the query-batch request, and executing that request against the retained root
has the typed pre-answer fork witness above. -/
theorem deployed_root_sweep_covers_query_batch_typed_fork
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (totalLimitMono : machine.adversaryLimits.totalCalls ≤
      configuration.oracleLimits.totalCalls)
    (freshLimitMono : machine.adversaryLimits.freshCalls ≤
      configuration.oracleLimits.freshCalls)
    (rounds : Nat) (roundsPositive : 0 < rounds)
    (result : Result) (requests : List ConcreteRestorationRequest)
    (path : ConcreteRequestPath (deployedRootSweepClient rounds result)
      requests)
    (transitionIndex : Nat) (transitionWithin : transitionIndex < 1513)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (block : Nat) (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) block) reply)
    (environment : FutureFreeEnvironment)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    { nodeId := 0, verifierTransitionIndex := transitionIndex } ∈ requests ∧
      ∃ (prepared : PreparedConcreteRestoration Statement Proof Payload)
          (role : PreparedRestorationPairRole),
        prepareConcreteRestorationFromStartProgram
            (machine.blackBox.start hidden machine.observation) configuration
            accumulator
            { nodeId := 0, verifierTransitionIndex := transitionIndex } =
          .ready prepared ∧
        HistoryTotalCoherent prepared.programmingBase ∧
        prepared.transition = transition ∧
        preparedRestorationPairRole? prepared = some role ∧
        role.owner = .challenge .queryBatch ∧
        role.block = block ∧
        role.outputInput =
          bytes transition.before.core.digest ++ [domSqueeze] ∧
        role.advanceInput =
          bytes transition.before.core.digest ++ [domAdvance] ∧
        (configuration.oracleLimits.totalCalls ≤ globalOracleCalls →
          prepared.programmingBase.history.length + 2 ≤ globalOracleCalls →
          schedulerNativePairForkHeader?
              (dispatchOneConcreteRestoration
                (machine.blackBox.start hidden machine.observation) environment
                configuration accumulator
                { nodeId := 0, verifierTransitionIndex := transitionIndex }
                resume) =
            some (preparedForkHeader configuration prepared)) := by
  constructor
  · exact deployed_root_sweep_every_path_covers_transition rounds result path
      roundsPositive transitionIndex transitionWithin
  · exact literal_root_query_batch_dispatch_emits_typed_fork machine hidden
      runtime runs configuration totalLimitMono freshLimitMono transitionIndex
      transition transitionExact block reply eventExact environment accumulator
      rootStored resume

/-! ## Exact master-tape coordinates at the typed fork -/

/-- A cursor whose first-phase fork header is known consumes the next two
master-tape coordinates as the output and advance answers of that exact
header.  In particular, the fork output cannot inspect the advance answer:
the latter is still the head of the remaining tape when the first record is
emitted. -/
theorem pair_fork_header_exposes_exact_adjacent_coordinates
    {globalOracleCalls remaining : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (header : PreparedForkHeader)
    (headerExact : schedulerNativePairForkHeader? cursor = some header)
    (forkOutput forkAdvance : Digest256)
    (tail : FreshAnswerTape Digest256 remaining) :
    ∃ (pairRoom : header.frozenHistory.length + 2 ≤ globalOracleCalls)
        (next : AtomicPairReplayConfiguration →
          SchedulerNativeCursor globalOracleCalls Result),
      cursor =
        .forkPair header.frozenHistory pairRoom header.outputInput
          header.advanceInput header.template next ∧
      (runSchedulerNative (transitionFuel + 1) (remaining + 2) cursor
          (forkOutput, (forkAdvance, tail))).trace =
        .forkOutput header.frozenHistory header.outputInput
            header.advanceInput header.template forkOutput ::
          .forkAdvance
            { frozenHistory := header.frozenHistory
              outputInput := header.outputInput
              advanceInput := header.advanceInput
              template := header.template
              forkOutput := forkOutput
              forkAdvance := forkAdvance } ::
          (runSchedulerNative (transitionFuel + 1) remaining
            (next (scheduledForkConfiguration header.template forkOutput
              forkAdvance)) tail).trace := by
  cases cursor with
  | machine => simp [schedulerNativePairForkHeader?] at headerExact
  | forkPair frozenHistory pairRoom outputInput advanceInput template next =>
      simp only [schedulerNativePairForkHeader?] at headerExact
      cases headerExact
      exact ⟨pairRoom, next, rfl, rfl⟩
  | forkAdvance => simp [schedulerNativePairForkHeader?] at headerExact
  | returned => simp [schedulerNativePairForkHeader?] at headerExact
  | failed => simp [schedulerNativePairForkHeader?] at headerExact

#print axioms literal_root_query_batch_dispatch_emits_typed_fork
#print axioms deployed_root_sweep_covers_query_batch_typed_fork
#print axioms pair_fork_header_exposes_exact_adjacent_coordinates

end
end AspisK1.V7Tag73RootQueryBatchForkBridge

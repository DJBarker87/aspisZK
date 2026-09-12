import AspisFormal.K1.V7Tag73ConcreteRootSweepClient
import AspisFormal.K1.V7Tag73ConcreteRestorationTraceInduction
import AspisFormal.K1.V7Tag73ExactCompilerOperationalCaps
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.K1.V7Tag73ExactLegalSameTapeEvent
import AspisFormal.K1.V7Tag73RootSqueezeForkEmission

/-!
# Root-sweep bridge to a typed gamma fork

The raw SHA input alone does not identify a Tag-73 challenge role: an
adversary may expose the same coordinate before the verifier reaches it.  The
state-restoration preparer has a stronger source of information.  It selects
one literal verifier transition before either uniform fork coin is exposed,
and that transition retains the exact `SqueezeOwner` and sampler block.

This module specializes the generic root-squeeze dispatcher theorem to the
gamma challenge and joins it to the deployed exhaustive root sweep.
The result is deterministic.  It neither assumes freshness nor assigns a
probability to a fork response.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RootGammaForkBridge

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRestorationTraceInduction
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactLegalSameTapeEvent
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawFutureFreeDriver
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

/-! ## The literal deployed root contains the typed gamma transition -/

/-- Exact source acceptance does not merely decode the gamma challenge:
the actual completed root runtime contains its block-zero verifier transition
strictly below the independently derived canonical driver-fuel cap.  Retaining
this stronger bound is important for the variable-prefix gamma argument: the
deployed 1513-position sweep has genuine suffix room after the selected
transition, rather than merely containing it. -/
theorem exact_clean_root_has_indexed_gamma_transition_with_canonical_bound
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {sample : ExactCompilerSample HiddenTape parameters}
    (root : ExactCleanSourceRootProjection transitionFuel configuration
      projection sample) :
    ∃ transitionIndex transition reply,
      verifierTransitionAt? root.runtime.node transitionIndex =
          some transition ∧
        transitionIndex < tag73CanonicalDriverFuelCap ∧
        transitionIndex < 1513 ∧
        transition.event =
          .verifier (.squeezePair (.challenge .gamma) 0) reply := by
  obtain ⟨transition, reply, transitionMember, eventExact⟩ :=
    root.canonical.construction.gammaTransitionExact
  have finalStateExact : root.canonical.construction.complete.final =
      root.runtime.verifierFinalState :=
    root.actualPathAlignment.finalStateExact.symm.trans
      root.projected.finalStateExact
  rw [finalStateExact] at transitionMember
  rw [List.mem_iff_getElem] at transitionMember
  obtain ⟨transitionIndex, within, valueExact⟩ := transitionMember
  have transitionCount :
      root.canonical.construction.complete.final.transitions.length ≤
        root.canonical.construction.complete.fuel := by
    have growth := drive_raw_future_free_transition_growth_le_fuel
      (fixedTapeFutureFreeEnvironment root.tape)
      (fixedTapeRawMessages root.tape)
      root.canonical.construction.complete.fuel
      (initialFutureFreeVerifierState
        (FixedBindings.ofContext root.tape.messages.context))
      root.canonical.construction.complete.pairs
      root.canonical.construction.complete.final
      (by simpa [initialRawFutureFreeProgram] using
        root.canonical.construction.complete.path)
    simpa [initialFutureFreeVerifierState] using growth
  have runtimeTransitionCount :
      root.runtime.verifierFinalState.transitions.length ≤
        root.canonical.construction.complete.fuel := by
    rw [← finalStateExact]
    exact transitionCount
  have indexWithinCanonical :
      transitionIndex < tag73CanonicalDriverFuelCap := by
    have cap := root.canonical.fuelWithinProtocolCap
    omega
  have indexWithin : transitionIndex < 1513 := by
    have protocolCap : tag73CanonicalDriverFuelCap < 1513 := by decide
    omega
  refine ⟨transitionIndex, transition, reply, ?_, indexWithinCanonical,
    indexWithin, eventExact⟩
  unfold verifierTransitionAt?
  rw [List.getElem?_eq_some_iff]
  exact ⟨within, valueExact⟩

/-- Compatibility form used by the deployed 1513-position sweep. -/
theorem exact_clean_root_has_indexed_gamma_transition
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {sample : ExactCompilerSample HiddenTape parameters}
    (root : ExactCleanSourceRootProjection transitionFuel configuration
      projection sample) :
    ∃ transitionIndex transition reply,
      verifierTransitionAt? root.runtime.node transitionIndex =
          some transition ∧
        transitionIndex < 1513 ∧
        transition.event =
          .verifier (.squeezePair (.challenge .gamma) 0) reply := by
  obtain ⟨transitionIndex, transition, reply, transitionExact,
      _indexWithinCanonical, indexWithin, eventExact⟩ :=
    exact_clean_root_has_indexed_gamma_transition_with_canonical_bound root
  exact ⟨transitionIndex, transition, reply, transitionExact, indexWithin,
    eventExact⟩

/-- A selected root gamma transition emits a fork whose typed owner and
block are fixed before either fork answer is exposed. -/
theorem literal_root_gamma_dispatch_emits_typed_fork
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
      .verifier (.squeezePair (.challenge .gamma) block) reply)
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
      prepared.programmingBase.history.length ≤ machine.adversaryFuel ∧
      prepared.transition = transition ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.owner = .challenge .gamma ∧
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
  obtain ⟨prepared, role, ready, coherent, historyBound, projected, _inputs,
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
      { owner := .challenge .gamma
        block := block
        outputInput := prepared.outputInput
        advanceInput := prepared.advanceInput } := by
    unfold preparedRestorationPairRole? at projected
    rw [preparedTransitionExact, eventExact] at projected
    exact Option.some.inj projected.symm
  subst role
  refine ⟨prepared,
    { owner := .challenge .gamma
      block := block
      outputInput := prepared.outputInput
      advanceInput := prepared.advanceInput },
    ready, coherent, historyBound, preparedTransitionExact, projected, rfl,
    rfl, ?_, ?_, emits⟩
  · simpa [preparedTransitionExact] using outputExact
  · simpa [preparedTransitionExact] using advanceExact

/-- The typed gamma specialization also inherits the stronger literal
root replay guarantee: every pair of fork answers can be installed at the
actual gamma transition, including when the adversary queried either
SHA input in the original execution.  In that case the preparer replays the
root only to the strict prefix before first exposure, where both inputs are
proved absent.  No freshness, role-classification, or probability premise is
left to the caller. -/
theorem literal_root_gamma_dispatch_programs_every_fork_pair
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
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
      .verifier (.squeezePair (.challenge .gamma) block) reply)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (rootStored : accumulator.node? 0 = some runtime.node)
    (forkOutput forkAdvance : Digest256)
    (programmingRoom : 2 ≤ configuration.oracleLimits.programmedPoints) :
    ∃ (prepared : PreparedConcreteRestoration Statement Proof Payload)
        (role : PreparedRestorationPairRole) (afterBoth : OracleState),
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      prepared.transition = transition ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.owner = .challenge .gamma ∧
      role.block = block ∧
      role.outputInput =
        bytes transition.before.core.digest ++ [domSqueeze] ∧
      role.advanceInput =
        bytes transition.before.core.digest ++ [domAdvance] ∧
      programConcretePair configuration.oracleLimits
          configuration.pairProgrammingOrder prepared.programmingBase
          prepared.outputInput prepared.advanceInput forkOutput forkAdvance =
        .ready afterBoth := by
  let outputInput := bytes transition.before.core.digest ++ [domSqueeze]
  let advanceInput := bytes transition.before.core.digest ++ [domAdvance]
  have pairExact : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput) := by
    rw [squeezePairInputsOfTransition, eventExact]
  obtain ⟨prepared, afterBoth, ready, coherent, programmed⟩ :=
    literal_root_squeeze_request_programs_every_fork_pair machine hidden
      runtime runs configuration totalLimitMono freshLimitMono transitionIndex
      transition transitionExact outputInput advanceInput pairExact accumulator
      rootStored forkOutput forkAdvance programmingRoom
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
  let role : PreparedRestorationPairRole :=
    { owner := .challenge .gamma
      block := block
      outputInput := prepared.outputInput
      advanceInput := prepared.advanceInput }
  have roleExact : preparedRestorationPairRole? prepared = some role := by
    unfold preparedRestorationPairRole? role
    rw [preparedTransitionExact, eventExact]
  have preparedPair := prepare_from_start_ready_pair_inputs_exact
    (machine.blackBox.start hidden machine.observation) configuration accumulator
    { nodeId := 0, verifierTransitionIndex := transitionIndex } prepared ready
  rw [preparedTransitionExact, pairExact] at preparedPair
  have pairComponents : outputInput = prepared.outputInput ∧
      advanceInput = prepared.advanceInput :=
    Prod.mk.inj (Option.some.inj preparedPair)
  have outputExact : prepared.outputInput = outputInput := by
    exact pairComponents.1.symm
  have advanceExact : prepared.advanceInput = advanceInput := by
    exact pairComponents.2.symm
  exact ⟨prepared, role, afterBoth, ready, coherent,
    preparedTransitionExact, roleExact, rfl, rfl,
    outputExact, advanceExact, programmed⟩

/-- Proof-relevant operational package for the exact block-zero gamma
fork selected from an accepted clean root.  This is the source object needed
by the K1.3 finite-field fibre: the fork answers are parameters, while the
typed transition and its strict pre-exposure programming base are derived. -/
structure ExactOperationalGammaProgrammableFork
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (accumulator : ConcreteRestorationAccumulator Statement Tag73K12ParsedProof
      Payload)
    (forkOutput forkAdvance : Digest256) : Type where
  transitionIndex : Nat
  transition : FutureFreeTransition
  reply : VerifierReply
  transitionExact : verifierTransitionAt?
    input.package.root.fixedRoot.base.runtime.node transitionIndex =
      some transition
  transitionWithin : transitionIndex < 1513
  eventExact : transition.event =
    .verifier (.squeezePair (.challenge .gamma) 0) reply
  prepared : PreparedConcreteRestoration Statement Tag73K12ParsedProof Payload
  role : PreparedRestorationPairRole
  afterBoth : OracleState
  ready : prepareConcreteRestorationFromStartProgram
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.restorationConfiguration accumulator
      { nodeId := 0, verifierTransitionIndex := transitionIndex } =
    .ready prepared
  coherent : HistoryTotalCoherent prepared.programmingBase
  transitionPrepared : prepared.transition = transition
  roleExact : preparedRestorationPairRole? prepared = some role
  ownerExact : role.owner = .challenge .gamma
  blockExact : role.block = 0
  outputInputExact : role.outputInput =
    bytes transition.before.core.digest ++ [domSqueeze]
  advanceInputExact : role.advanceInput =
    bytes transition.before.core.digest ++ [domAdvance]
  programmed : programConcretePair
      configuration.restorationConfiguration.oracleLimits
      configuration.restorationConfiguration.pairProgrammingOrder
      prepared.programmingBase prepared.outputInput prepared.advanceInput
      forkOutput forkAdvance = .ready afterBoth

/-- Every accepted operational K1.2 input exposes a genuinely programmable
gamma fork for arbitrary output and advance coins.  In particular the
adversary-first/cache-hit case is not a source premise: the literal root
replay moves the programming base to the strict prefix before first exposure
and proves both lookups absent there. -/
theorem exact_operational_gamma_programs_every_fork_pair
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel configuration)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (accumulator : ConcreteRestorationAccumulator Statement Tag73K12ParsedProof
      Payload)
    (rootStored : accumulator.node? 0 =
      some input.package.root.fixedRoot.base.runtime.node)
    (forkOutput forkAdvance : Digest256)
    (programmingRoom : 2 ≤
      configuration.restorationConfiguration.oracleLimits.programmedPoints) :
    Nonempty (ExactOperationalGammaProgrammableFork input accumulator
      forkOutput forkAdvance) := by
  let root := input.package.root.fixedRoot.base
  let runtime := root.runtime
  obtain ⟨transitionIndex, transition, reply, transitionExact,
      transitionWithin, eventExact⟩ :=
    exact_clean_root_has_indexed_gamma_transition root
  have runs : RootProjectedTotalizedRuns configuration.machine sample.1
      runtime :=
    completed_exact_plain_rom_root_gives_projected_totalized_runs
      transitionFuel (by omega) configuration sample runtime root.clientRun
        root.rootCompleted
  have limitMono :=
    adequate_replay_limits_extend_root_adversary configuration adequate
  obtain ⟨prepared, role, afterBoth, ready, coherent,
      transitionPrepared, roleExact, ownerExact, blockExact,
      outputInputExact, advanceInputExact, programmed⟩ :=
    literal_root_gamma_dispatch_programs_every_fork_pair
      configuration.machine sample.1 runtime runs
      configuration.restorationConfiguration
      limitMono.1 limitMono.2 transitionIndex transition
      transitionExact 0 reply eventExact accumulator (by simpa [runtime])
      forkOutput forkAdvance programmingRoom
  exact ⟨⟨transitionIndex, transition, reply, by simpa [runtime] using
      transitionExact, transitionWithin, eventExact, prepared, role, afterBoth,
      ready, coherent, transitionPrepared, roleExact, ownerExact, blockExact,
      outputInputExact, advanceInputExact, programmed⟩⟩

/-- Every adaptive reply path through a positive deployed root sweep contains
the gamma request, and executing that request against the retained root
has the typed pre-answer fork witness above. -/
theorem deployed_root_sweep_covers_gamma_typed_fork
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
      .verifier (.squeezePair (.challenge .gamma) block) reply)
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
        prepared.programmingBase.history.length ≤ machine.adversaryFuel ∧
        prepared.transition = transition ∧
        preparedRestorationPairRole? prepared = some role ∧
        role.owner = .challenge .gamma ∧
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
  · exact literal_root_gamma_dispatch_emits_typed_fork machine hidden
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

#print axioms
  exact_clean_root_has_indexed_gamma_transition_with_canonical_bound
#print axioms exact_clean_root_has_indexed_gamma_transition
#print axioms literal_root_gamma_dispatch_emits_typed_fork
#print axioms literal_root_gamma_dispatch_programs_every_fork_pair
#print axioms exact_operational_gamma_programs_every_fork_pair
#print axioms deployed_root_sweep_covers_gamma_typed_fork
#print axioms pair_fork_header_exposes_exact_adjacent_coordinates

end
end AspisK1.V7Tag73RootGammaForkBridge

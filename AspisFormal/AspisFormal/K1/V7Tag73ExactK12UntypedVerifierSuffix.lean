import AspisFormal.K1.V7Tag73ExactFixedK12PrefixClassifier
import AspisFormal.K1.V7Tag73K12BudgetedSchedulerTree
import AspisFormal.K1.V7Tag73SharedShaGrammar
import AspisFormal.K1.V7Tag73CumulativeReplayHistory
import AspisFormal.Pool.V7MerkleCompletePrefixStability

/-!
# The post-prover Tag-73 verifier log is not Merkle grammar

This file identifies the exact suffix added after the prover's shared-oracle
history and proves that every input in it is a transcript-machine input, hence
cannot parse as a 437-, 220-, or 53-byte Tag-73 Merkle preimage.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactK12UntypedVerifierSuffix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73SharedShaGrammar
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar

noncomputable section

theorem parseTypedPreimage_none_of_length_avoids
    (input : RawHashInput)
    (avoids : input.length ≠ 437 ∧ input.length ≠ 220 ∧
      input.length ≠ 53) :
    parseTypedPreimage input = none := by
  simp [parseTypedPreimage, avoids.1, avoids.2.1, avoids.2.2]

theorem raw_query_role_input_is_untyped
    (before : Digest256) (role : RawQueryRole) :
    parseTypedPreimage
      (runtimeInputToRawHashInput (role.input before)) = none := by
  apply parseTypedPreimage_none_of_length_avoids
  simpa [runtimeInputToRawHashInput] using
    (raw_query_input_length_avoids_typed_merkle before role)

theorem future_free_reply_program_path_inputs_exact
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath (futureFreeReplyProgram state action) pairs reply) :
    pairs.map Prod.fst =
      actionInputs state.current.bindings state.current.core action := by
  cases action with
  | absorb payload =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | requestRootSalt tree =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | absorbC1 root =>
      cases saltExact : state.current.core.c1Salt with
      | none =>
          simp [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path
          cases path
      | some salt =>
          simp only [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path ⊢
          cases path with
          | query _ _ output _ _ tail => cases tail; rfl
  | absorbC2 lambda chi commitment =>
      cases saltExact : state.current.core.c2Salt with
      | none =>
          simp [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path
          cases path
      | some salt =>
          simp only [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path ⊢
          cases path with
          | query _ _ output _ _ tail => cases tail; rfl
  | squeezePair owner block =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail =>
          cases tail with
          | query _ _ advance _ _ final => cases final; rfl
  | workProbe stage nonce kind =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | checkpoint checkpoint => cases path; rfl
  | markQ16Base => cases path; rfl
  | q16CandidateAbsorb counter outcome selected =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | q16Restore counter => cases path; rfl
  | q16Selected counter => cases path; rfl
  | q16SamplerAbortReject counter => cases path; rfl
  | q16AllNoncompactReject => cases path; rfl
  | terminal => cases path; rfl

def futureFreeActionRoles (bindings : FixedBindings) (core : RuntimeCore) :
    VerifierAction → List RawQueryRole
  | .absorb payload => [.absorb payload]
  | .requestRootSalt tree => [.publicRootSalt bindings.context tree.tag]
  | .absorbC1 root =>
      match core.c1Salt with
      | none => []
      | some salt => [.absorb (Payload.c1Root root.value salt)]
  | .absorbC2 _lambda _chi commitment =>
      match core.c2Salt with
      | none => []
      | some salt => [.absorb (Payload.c2Root commitment.root salt)]
  | .squeezePair owner block =>
      [.squeezeOutput owner block, .squeezeAdvance owner block]
  | .workProbe stage nonce _kind => [.grind stage nonce]
  | .checkpoint _ | .markQ16Base | .q16Restore _ | .q16Selected _ |
      .q16SamplerAbortReject _ | .q16AllNoncompactReject | .terminal => []
  | .q16CandidateAbsorb counter _outcome _selected =>
      [.absorb (.queryCandidate counter)]

theorem future_free_action_roles_inputs_exact
    (bindings : FixedBindings) (core : RuntimeCore) (action : VerifierAction) :
    (futureFreeActionRoles bindings core action).map
        (RawQueryRole.input core.digest) =
      actionInputs bindings core action := by
  cases action with
  | absorb payload => rfl
  | requestRootSalt tree => rfl
  | absorbC1 root =>
      cases saltExact : core.c1Salt <;>
        simp [futureFreeActionRoles, actionInputs, RawQueryRole.input,
          Payload.label, saltExact]
  | absorbC2 lambda chi commitment =>
      cases saltExact : core.c2Salt <;>
        simp [futureFreeActionRoles, actionInputs, RawQueryRole.input,
          Payload.label, saltExact]
  | squeezePair owner block => rfl
  | workProbe stage nonce kind => rfl
  | checkpoint checkpoint => rfl
  | markQ16Base => rfl
  | q16CandidateAbsorb counter outcome selected => rfl
  | q16Restore counter => rfl
  | q16Selected counter => rfl
  | q16SamplerAbortReject counter => rfl
  | q16AllNoncompactReject => rfl
  | terminal => rfl

theorem future_free_action_input_is_untyped
    (bindings : FixedBindings) (core : RuntimeCore) (action : VerifierAction)
    (input : ShaInput) (member : input ∈ actionInputs bindings core action) :
    parseTypedPreimage (runtimeInputToRawHashInput input) = none := by
  rw [← future_free_action_roles_inputs_exact bindings core action] at member
  obtain ⟨role, _roleMember, rfl⟩ := List.mem_map.mp member
  exact raw_query_role_input_is_untyped core.digest role

theorem future_free_reply_program_path_inputs_untyped
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath (futureFreeReplyProgram state action) pairs reply) :
    ∀ pair ∈ pairs,
      parseTypedPreimage (runtimeInputToRawHashInput pair.1) = none := by
  have inputsExact := future_free_reply_program_path_inputs_exact state action
    pairs reply path
  intro pair member
  have inputMember : pair.1 ∈ pairs.map Prod.fst := List.mem_map_of_mem member
  rw [inputsExact] at inputMember
  exact future_free_action_input_is_untyped state.current.bindings
    state.current.core action pair.1 inputMember

theorem future_free_operational_trace_inputs_untyped
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ (initial final : FutureFreeVerifierState)
      (pairs : List (ShaInput × ShaOutput)),
      FutureFreeOperationalTrace environment raw initial pairs final →
      ∀ pair ∈ pairs,
        parseTypedPreimage (runtimeInputToRawHashInput pair.1) = none := by
  intro initial final pairs trace
  induction trace with
  | stop state => simp
  | next step rest ih =>
      intro pair member
      rw [List.mem_append] at member
      rcases member with headMember | tailMember
      · cases step with
        | prover submitted event snapshot appendExact => simp at headMember
        | verifier forced replyPath advanced =>
            exact future_free_reply_program_path_inputs_untyped _ _ _ _
              replyPath pair headMember
        | stutter noSubmission noAction => simp at headMember
      · exact ih pair tailMember

/-! ## Exact root-history decomposition -/

/-- The exact K1.2 query log is the completed prover history followed by a
suffix containing only transcript-machine inputs.  This is stronger than a
mere prefix statement: it identifies every post-prover raw input as outside
the deployed Merkle grammar. -/
theorem exact_k12_ordered_queries_eq_prover_prefix_append_untyped
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ suffix : OrderedRawQueryLog,
      exactK12OrderedQueries input =
          exactK12ProverPrefixQueries input ++ suffix ∧
        ∀ rawInput ∈ suffix, parseTypedPreimage rawInput = none := by
  let runtime := exactK12Runtime input
  let projected := input.package.root.fixedRoot.base.projected
  let execution := projected.execution
  obtain ⟨adversarySteps, _verifierSteps, adversaryRun, _verifierRun⟩ :=
    input.package.root.full.projection.projectedRuns
  have reflectedAdversary := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime)
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have proverOracleExact :
      (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle =
        runtime.proverFinalOracle := by
    change
      (runMachine (rootAdversaryProjectedController runtime)
        configuration.machine.adversaryLimits .adversary
        configuration.machine.adversaryFuel emptyOracle
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)).oracle =
      runtime.proverFinalOracle
    rw [reflectedAdversary]
  have verifierOracleExact : execution.verifierRun.oracle =
      runtime.verifierFinalOracle := by
    exact projected.finalOracleExact
  obtain ⟨pairs, historyExact, operational⟩ :=
    raw_verifier_execution_has_operational_trace execution
  have pairsUntyped := future_free_operational_trace_inputs_untyped
    execution.environment execution.adversaryValue.rawMessages
    _ _ pairs operational
  have chronological := run_machine_history_since_is_chronological_suffix
    execution.verifierController execution.verifierLimits .verifier
    execution.verifierFuel
    (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle
    (initialRawFutureFreeProgram execution.environment
      execution.adversaryValue.rawMessages execution.driverFuel)
  let suffix : OrderedRawQueryLog := execution.verifierHistory.map
    (fun record => runtimeInputToRawHashInput record.input)
  refine ⟨suffix, ?_, ?_⟩
  · unfold exactK12OrderedQueries exactK12ProverPrefixQueries
    change runtime.verifierFinalOracle.history.map _ =
      runtime.proverFinalOracle.history.map _ ++ suffix
    have historyAppend : runtime.verifierFinalOracle.history =
        runtime.proverFinalOracle.history ++ execution.verifierHistory := by
      have exact := chronological.1
      change execution.verifierRun.oracle.history =
        (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle.history ++
          execution.verifierHistory at exact
      rw [proverOracleExact, verifierOracleExact] at exact
      exact exact
    rw [historyAppend, List.map_append]
  · intro rawInput member
    obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp member
    have pairMember : (record.input, record.output) ∈ pairs := by
      rw [← historyExact]
      exact List.mem_map.mpr ⟨record, recordMember, rfl⟩
    exact pairsUntyped (record.input, record.output) pairMember

/-- The canonical 208-bit view frozen at prover return, before any verifier
transcript query is made. -/
def exactK12ProverTruncate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : RawHashInput →
        AspisPool.V7MerkleQueryGrammar.Digest208 :=
  truncateAtOracleState (exactK12Runtime input).proverFinalOracle

/-- The verifier-final and prover-final views agree on every input accepted by
the Merkle grammar.  A genuinely new verifier table entry has a matching
operational verifier call, and the exact driver theorem makes that call
untyped; cached entries already belong to the prover-final table. -/
theorem exact_k12_truncate_eq_prover_truncate_on_typed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (rawInput : RawHashInput)
    (typed : parseTypedPreimage rawInput ≠ none) :
    exactK12Truncate input rawInput = exactK12ProverTruncate input rawInput := by
  let runtime := exactK12Runtime input
  let projected := input.package.root.fixedRoot.base.projected
  let execution := projected.execution
  obtain ⟨adversarySteps, _verifierSteps, adversaryRun, _verifierRun⟩ :=
    input.package.root.full.projection.projectedRuns
  have reflectedAdversary := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime)
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have proverOracleExact :
      (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle =
        runtime.proverFinalOracle := by
    change
      (runMachine (rootAdversaryProjectedController runtime)
        configuration.machine.adversaryLimits .adversary
        configuration.machine.adversaryFuel emptyOracle
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)).oracle =
      runtime.proverFinalOracle
    rw [reflectedAdversary]
  have proverOracleExactInput :
      (projectedRootSource configuration.machine sample.1
        input.package.root.fixedRoot.base.runtime).firstExecution.oracle =
      input.package.root.fixedRoot.base.runtime.proverFinalOracle := by
    change
      (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle =
        runtime.proverFinalOracle
    exact proverOracleExact
  have verifierOracleExact : execution.verifierRun.oracle =
      runtime.verifierFinalOracle := projected.finalOracleExact
  have verifierOracleExactRun :
      (runMachine execution.verifierController execution.verifierLimits
        .verifier execution.verifierFuel runtime.proverFinalOracle
        (initialRawFutureFreeProgram execution.environment
          execution.adversaryValue.rawMessages execution.driverFuel)).oracle =
        runtime.verifierFinalOracle := by
    have exact := verifierOracleExact
    unfold RawVerifierExecution.verifierRun at exact
    rw [proverOracleExactInput] at exact
    exact exact
  obtain ⟨pairs, historyExact, operational⟩ :=
    raw_verifier_execution_has_operational_trace execution
  have pairsUntyped := future_free_operational_trace_inputs_untyped
    execution.environment execution.adversaryValue.rawMessages
    _ _ pairs operational
  let tableSuffix := verifierFreshTableEntries
    runtime.proverFinalOracle runtime.verifierFinalOracle
  have tableExtension := (run_machine_exact_fresh_extension execution.verifierController
      execution.verifierLimits .verifier execution.verifierFuel
      (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle
      (initialRawFutureFreeProgram execution.environment
        execution.adversaryValue.rawMessages execution.driverFuel)).1
  have tableExtension' : runtime.verifierFinalOracle.table =
      runtime.proverFinalOracle.table ++ tableSuffix := by
    rw [proverOracleExact] at tableExtension
    rw [verifierOracleExactRun] at tableExtension
    simpa [tableSuffix] using tableExtension
  let runtimeInput := rawHashInputToRuntimeInput rawInput
  cases beforeLookup : lookupEntry runtime.proverFinalOracle runtimeInput with
  | some entry =>
      have afterLookup := lookupEntry_preserved_by_table_extension
        runtime.proverFinalOracle runtime.verifierFinalOracle tableSuffix
        tableExtension' runtimeInput entry beforeLookup
      simp [exactK12Truncate, exactK12ProverTruncate, truncateAtOracleState,
        runtime, runtimeInput, beforeLookup, afterLookup]
  | none =>
      cases afterLookup : lookupEntry runtime.verifierFinalOracle runtimeInput with
      | none =>
          simp [exactK12Truncate, exactK12ProverTruncate,
            truncateAtOracleState, runtime, runtimeInput, beforeLookup,
            afterLookup]
      | some entry =>
          have newMember := lookupEntry_new_suffix_member
            runtime.proverFinalOracle runtime.verifierFinalOracle tableSuffix
            tableExtension' runtimeInput entry beforeLookup afterLookup
          have newEntry := run_machine_new_entry_is_fresh_and_initially_absent
            execution.verifierController execution.verifierLimits .verifier
            execution.verifierFuel
            (projectedRootSource configuration.machine sample.1 runtime).firstExecution.oracle
            (initialRawFutureFreeProgram execution.environment
              execution.adversaryValue.rawMessages execution.driverFuel)
            entry (by
              rw [proverOracleExact, verifierOracleExactRun]
              exact newMember)
          obtain ⟨record, recordMember, _actor, _fresh, recordInput,
              _recordOutput, _entryExact⟩ := newEntry.2.2
          have pairMember : (record.input, record.output) ∈ pairs := by
            rw [← historyExact]
            have recordMember' : record ∈ execution.verifierHistory := by
              unfold RawVerifierExecution.verifierHistory
              exact recordMember
            exact List.mem_map.mpr ⟨record, recordMember', rfl⟩
          have untyped := pairsUntyped (record.input, record.output) pairMember
          have entryInput : entry.input = runtimeInput := by
            unfold lookupEntry at afterLookup
            exact of_decide_eq_true
              (List.find?_eq_some_iff_append.mp afterLookup).1
          have rawExact : runtimeInputToRawHashInput record.input = rawInput := by
            rw [recordInput, entryInput]
            exact runtimeInputToRawHashInput_roundtrip rawInput
          exact False.elim (typed (by simpa [rawExact] using untyped))

#print axioms raw_query_role_input_is_untyped
#print axioms exact_k12_ordered_queries_eq_prover_prefix_append_untyped
#print axioms exact_k12_truncate_eq_prover_truncate_on_typed

end

end AspisK1.V7Tag73ExactK12UntypedVerifierSuffix

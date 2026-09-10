import AspisFormal.K1.V7Tag73RestoredQueryBatchCausalMarker

/-!
# Causal marker for a typed restored challenge fork

The query-batch marker is one instance of a more general restoration fact:
the selected verifier squeeze owner and block are present in the prepared
transition before either replacement answer is sampled.  This module exposes
that fact for an arbitrary expected owner and specializes it to the block-zero
gamma fork used by the K1.4/K1.5 probability coordinates.

This deliberately does not classify a raw SHA input.  In particular, an
adversary-first cache hit in the root execution is irrelevant: the marker is
attached only to the executable restoration dispatcher which has already
selected the typed verifier transition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredChallengeCausalMarker

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RestoredQueryBatchForkController
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

/-- Proof-relevant recognition of a ready restored block-zero squeeze whose
owner is fixed before either fork answer. -/
def IsTypedRestoredChallengeForkStart
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Prop :=
  ∃ (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (prepared : PreparedConcreteRestoration Statement Proof Payload)
      (role : PreparedRestorationPairRole)
      (resume : ConcreteRestorationReply →
        ConcreteRestorationAccumulator Statement Proof Payload →
          SchedulerNativeCursor globalOracleCalls
            (ConcreteRestorationClientRun Statement Proof Payload Result)),
    prepareConcreteRestorationFromStartProgram startProgram configuration
        accumulator prepared.request = .ready prepared ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.owner = expectedOwner ∧
      role.block = 0 ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      configuration.oracleLimits.totalCalls ≤ globalOracleCalls ∧
      prepared.programmingBase.history.length + 2 ≤ globalOracleCalls ∧
      cursor =
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase

/-- The same pre-answer marker with the concrete restoration request retained.
This is needed when a later algebraic stage must use the child created by one
particular verifier transition rather than an unrelated restored node. -/
def IsTypedRestoredChallengeForkStartForRequest
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (request : ConcreteRestorationRequest)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Prop :=
  ∃ (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (prepared : PreparedConcreteRestoration Statement Proof Payload)
      (role : PreparedRestorationPairRole)
      (resume : ConcreteRestorationReply →
        ConcreteRestorationAccumulator Statement Proof Payload →
          SchedulerNativeCursor globalOracleCalls
            (ConcreteRestorationClientRun Statement Proof Payload Result)),
    prepared.request = request ∧
      prepareConcreteRestorationFromStartProgram startProgram configuration
          accumulator prepared.request = .ready prepared ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.owner = expectedOwner ∧
      role.block = 0 ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      configuration.oracleLimits.totalCalls ≤ globalOracleCalls ∧
      prepared.programmingBase.history.length + 2 ≤ globalOracleCalls ∧
      cursor =
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase

theorem typed_restored_challenge_for_request_implies_marker
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (request : ConcreteRestorationRequest)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (exactRequest : IsTypedRestoredChallengeForkStartForRequest
      (Result := Result) expectedOwner request startProgram environment
        configuration cursor) :
    IsTypedRestoredChallengeForkStart (Result := Result) expectedOwner
      startProgram environment configuration cursor := by
  rcases exactRequest with ⟨accumulator, prepared, role, resume, _requestExact,
    ready, roleExact, ownerExact, blockExact, coherent, globalRoom, pairRoom,
    cursorExact⟩
  exact ⟨accumulator, prepared, role, resume, ready, roleExact, ownerExact,
    blockExact, coherent, globalRoom, pairRoom, cursorExact⟩

def typedRestoredChallengeForkStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool := by
  classical
  exact if IsTypedRestoredChallengeForkStart (Result := Result) expectedOwner
    startProgram environment configuration cursor then true else false

@[simp] theorem typed_restored_challenge_fork_starts_here_iff
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    typedRestoredChallengeForkStartsHere (Result := Result) expectedOwner
        startProgram environment configuration cursor = true ↔
      IsTypedRestoredChallengeForkStart (Result := Result) expectedOwner
        startProgram environment configuration cursor := by
  classical
  simp [typedRestoredChallengeForkStartsHere]

/-- A literal ready dispatcher is marked from its prepared role, without
examining either random replacement answer. -/
theorem typed_challenge_prepared_dispatch_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator prepared.request = .ready prepared)
    (roleExact : preparedRestorationPairRole? prepared = some role)
    (ownerExact : role.owner = expectedOwner)
    (blockExact : role.block = 0)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredChallengeForkStartsHere (Result := Result) expectedOwner
        startProgram environment configuration
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase = true := by
  rw [typed_restored_challenge_fork_starts_here_iff]
  exact ⟨accumulator, prepared, role, resume, ready, roleExact, ownerExact,
    blockExact, coherent, globalRoom, pairRoom, rfl⟩

theorem typed_challenge_dispatch_one_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator prepared.request = .ready prepared)
    (roleExact : preparedRestorationPairRole? prepared = some role)
    (ownerExact : role.owner = expectedOwner)
    (blockExact : role.block = 0)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredChallengeForkStartsHere (Result := Result) expectedOwner
        startProgram environment configuration
        (dispatchOneConcreteRestoration startProgram environment configuration
          accumulator prepared.request resume).erase = true := by
  simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration, ready]
  exact typed_challenge_prepared_dispatch_is_marked expectedOwner startProgram
    environment configuration accumulator prepared role resume ready roleExact
      ownerExact blockExact coherent globalRoom pairRoom

/-- A literal ready dispatch retains the exact request selected by its caller. -/
theorem typed_challenge_dispatch_one_starts_exact_request
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (request : ConcreteRestorationRequest)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (requestExact : prepared.request = request)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator prepared.request = .ready prepared)
    (roleExact : preparedRestorationPairRole? prepared = some role)
    (ownerExact : role.owner = expectedOwner)
    (blockExact : role.block = 0)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    IsTypedRestoredChallengeForkStartForRequest (Result := Result)
      expectedOwner request startProgram environment configuration
        (dispatchOneConcreteRestoration startProgram environment configuration
          accumulator prepared.request resume).erase := by
  simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration, ready]
  exact ⟨accumulator, prepared, role, resume, requestExact, ready, roleExact,
    ownerExact, blockExact, coherent, globalRoom, pairRoom, rfl⟩

theorem native_cursor_with_typed_challenge_marker_is_fork_pair
    {Statement Proof Payload ClientResult NativeResult : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : SchedulerNativeCursor globalOracleCalls NativeResult)
    (marked : typedRestoredChallengeForkStartsHere (Result := ClientResult)
      expectedOwner startProgram environment configuration cursor.erase = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor globalOracleCalls NativeResult),
      cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
        template next := by
  rw [typed_restored_challenge_fork_starts_here_iff] at marked
  rcases marked with ⟨accumulator, prepared, role, resume, ready, roleExact,
    ownerExact, blockExact, coherent, globalRoom, pairRoom, cursorExact⟩
  unfold dispatchPreparedRestoration at cursorExact
  rw [dif_pos coherent, dif_pos globalRoom, dif_pos pairRoom] at cursorExact
  cases cursor with
  | returned result => cases cursorExact
  | failed reason => cases cursorExact
  | machine limits limitBound actor state program fuel coherent onReturned =>
      cases cursorExact
  | forkPair frozenHistory nativePairRoom outputInput advanceInput template next =>
      exact ⟨frozenHistory, nativePairRoom, outputInput, advanceInput,
        template, next, rfl⟩
  | forkAdvance frozenHistory nativePairRoom outputInput advanceInput template
      forkOutput next =>
      cases cursorExact

theorem unified_cursor_with_typed_challenge_marker_is_fork_pair
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (marked : typedRestoredChallengeForkStartsHere (Result := Result)
      expectedOwner startProgram environment configuration cursor = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          UnifiedExposureCursor globalOracleCalls),
      cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
        template next := by
  rw [typed_restored_challenge_fork_starts_here_iff] at marked
  rcases marked with ⟨accumulator, prepared, role, resume, ready, roleExact,
    ownerExact, blockExact, coherent, globalRoom, pairRoom, cursorExact⟩
  subst cursor
  unfold dispatchPreparedRestoration
  rw [dif_pos coherent, dif_pos globalRoom, dif_pos pairRoom]
  exact ⟨prepared.programmingBase.history, pairRoom, prepared.outputInput,
    prepared.advanceInput, canonicalForkTemplate configuration, _, rfl⟩

/-- Exposure-normalized marker.  Deterministic cached work may be traversed
before the typed fork, but the record equality is required for every possible
answer and hence remains pre-answer. -/
def IsTypedRestoredChallengeExposureStart
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Prop :=
  ∃ target : UnifiedExposureCursor globalOracleCalls,
    IsTypedRestoredChallengeForkStart (Result := Result) expectedOwner
        startProgram environment configuration target ∧
      ∀ answer, unifiedRecordAtAnswer transitionFuel cursor answer =
        unifiedRecordAtAnswer transitionFuel target answer

def typedRestoredChallengeExposureStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool := by
  classical
  exact if IsTypedRestoredChallengeExposureStart (Result := Result)
    transitionFuel expectedOwner startProgram environment configuration cursor
  then true else false

def typedRestoredGammaForkStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool :=
  typedRestoredChallengeForkStartsHere (Result := Result) (.challenge .gamma)
    startProgram environment configuration cursor

def typedRestoredGammaExposureStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool :=
  typedRestoredChallengeExposureStartsHere (Result := Result) transitionFuel
    (.challenge .gamma) startProgram environment configuration cursor

theorem typed_gamma_dispatch_one_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator prepared.request = .ready prepared)
    (roleExact : preparedRestorationPairRole? prepared = some role)
    (ownerExact : role.owner = .challenge .gamma)
    (blockExact : role.block = 0)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredGammaForkStartsHere (Result := Result) startProgram
        environment configuration
        (dispatchOneConcreteRestoration startProgram environment configuration
          accumulator prepared.request resume).erase = true := by
  exact typed_challenge_dispatch_one_is_marked (.challenge .gamma) startProgram
    environment configuration accumulator prepared role resume ready roleExact
      ownerExact blockExact coherent globalRoom pairRoom

theorem native_cursor_with_typed_gamma_marker_is_fork_pair
    {Statement Proof Payload ClientResult NativeResult : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : SchedulerNativeCursor globalOracleCalls NativeResult)
    (marked : typedRestoredGammaForkStartsHere (Result := ClientResult)
      startProgram environment configuration cursor.erase = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor globalOracleCalls NativeResult),
      cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
        template next := by
  exact native_cursor_with_typed_challenge_marker_is_fork_pair
    (.challenge .gamma) startProgram environment configuration cursor marked

@[simp] theorem typed_restored_challenge_exposure_starts_here_iff
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    typedRestoredChallengeExposureStartsHere (Result := Result)
        transitionFuel expectedOwner startProgram environment configuration
        cursor = true ↔
      IsTypedRestoredChallengeExposureStart (Result := Result)
        transitionFuel expectedOwner startProgram environment configuration
        cursor := by
  classical
  simp [typedRestoredChallengeExposureStartsHere]

theorem typed_challenge_exposure_marked_of_record_eq
    {Statement Proof Payload Result : Type}
    {globalOracleCalls transitionFuel : Nat}
    (positive : 0 < transitionFuel)
    (expectedOwner : SqueezeOwner)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor target : UnifiedExposureCursor globalOracleCalls)
    (answer : Digest256)
    (targetMarked : typedRestoredChallengeForkStartsHere (Result := Result)
      expectedOwner startProgram environment configuration target = true)
    (recordExact : unifiedRecordAtAnswer transitionFuel cursor answer =
      unifiedRecordAtAnswer transitionFuel target answer) :
    typedRestoredChallengeExposureStartsHere (Result := Result)
        transitionFuel expectedOwner startProgram environment configuration
        cursor = true := by
  rw [typed_restored_challenge_exposure_starts_here_iff]
  rw [typed_restored_challenge_fork_starts_here_iff] at targetMarked
  refine ⟨target, targetMarked, ?_⟩
  obtain ⟨frozenHistory, pairRoom, outputInput, advanceInput, template, next,
      targetExact⟩ :=
    unified_cursor_with_typed_challenge_marker_is_fork_pair expectedOwner
      startProgram environment configuration target (by
        rw [typed_restored_challenge_fork_starts_here_iff]
        exact targetMarked)
  subst target
  cases transitionFuel with
  | zero => omega
  | succ fuel =>
      generalize requestExact : seekUnifiedExposure (fuel + 1) cursor = request
      cases request <;>
        simp only [unifiedRecordAtAnswer, requestExact, seekUnifiedExposure]
          at recordExact ⊢
      all_goals try { cases recordExact }
      intro other
      cases recordExact
      rfl

/-- The complete compiler tape factored at the first restored gamma block-zero
fork.  The 24 routed coordinates are the twelve output/advance pairs consumed
by the deployed gamma sampler. -/
def exactCompilerTypedRestoredGammaCoordinates
    {Statement Proof Payload Result : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerWaitingRestoredQueryBatchCoordinates parameters transitionFuel
    (typedRestoredChallengeExposureStartsHere (Result := Result)
      transitionFuel (.challenge .gamma) startProgram environment configuration)
    cursor

#print axioms IsTypedRestoredChallengeForkStart
#print axioms IsTypedRestoredChallengeForkStartForRequest
#print axioms typed_restored_challenge_for_request_implies_marker
#print axioms typed_restored_challenge_fork_starts_here_iff
#print axioms typed_challenge_prepared_dispatch_is_marked
#print axioms typed_challenge_dispatch_one_is_marked
#print axioms native_cursor_with_typed_challenge_marker_is_fork_pair
#print axioms unified_cursor_with_typed_challenge_marker_is_fork_pair
#print axioms IsTypedRestoredChallengeExposureStart
#print axioms typed_restored_challenge_exposure_starts_here_iff
#print axioms typed_challenge_exposure_marked_of_record_eq
#print axioms exactCompilerTypedRestoredGammaCoordinates
#print axioms typed_challenge_dispatch_one_starts_exact_request
#print axioms typed_gamma_dispatch_one_is_marked
#print axioms native_cursor_with_typed_gamma_marker_is_fork_pair

end
end AspisK1.V7Tag73RestoredChallengeCausalMarker

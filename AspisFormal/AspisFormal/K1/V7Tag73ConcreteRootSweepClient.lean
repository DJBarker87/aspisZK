import AspisFormal.K1.V7Tag73UniqueRestorationRequests
import AspisFormal.K1.V7Tag73SchedulerNativeSafety
import AspisFormal.K1.V7Tag73CompletedFullRunProjection
import AspisFormal.K1.V7Tag73ExactClientKnowledgeComposition
import AspisFormal.K1.V7Tag73ConcreteRestorationTraceInduction

/-!
# A finite root-transition sweep client for Tag-73 extraction

The deployed future-free verifier records a bounded list of transitions, but
the exact indices of squeeze transitions depend on the accepted execution.
The extractor must not guess a transcript role from a raw SHA coordinate:
an adversary may have queried that coordinate first.  Instead, the concrete
dispatcher accepts a verifier-transition index, derives the corresponding
pair of squeeze inputs from the stored snapshot, and replays the same-tape
prover to the first occurrence of either input.

This file constructs the finite client needed to exercise that dispatcher.
One sweep requests every root transition in a fixed half-open interval.
Nonexistent and non-squeeze indices fail closed and the client continues;
genuine squeeze indices create the controlled restoration nodes needed by the
K1.3--K1.5 probability arguments.  Repeated sweeps are supported because
ordinary extraction needs multiple independent responses at the same root
challenge and root nodes are immutable.

The construction is reply-insensitive.  Its exact request count and
replay-base-safe discipline are proved structurally, with no success,
probability, transcript-role, or extraction premise.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ConcreteRootSweepClient

open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73UniqueRestorationRequests
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeSafety
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73TranscriptSchedule

universe u

/-- Prepend requests for the root transitions
`start, start + 1, ..., start + count - 1` to an arbitrary client tail.
Every reply takes the same continuation. -/
def prependRootTransitionSweep {Result : Type u} (start : Nat) :
    (count : Nat) → ConcreteRestorationClient Result →
      ConcreteRestorationClient Result
  | 0, tail => tail
  | count + 1, tail =>
      .restore
        { nodeId := 0, verifierTransitionIndex := start }
        (fun _reply => prependRootTransitionSweep (start + 1) count tail)

@[simp] theorem prependRootTransitionSweep_zero
    {Result : Type u} (start : Nat)
    (tail : ConcreteRestorationClient Result) :
    prependRootTransitionSweep start 0 tail = tail := by
  rfl

@[simp] theorem prependRootTransitionSweep_succ
    {Result : Type u} (start count : Nat)
    (tail : ConcreteRestorationClient Result) :
    prependRootTransitionSweep start (count + 1) tail =
      .restore { nodeId := 0, verifierTransitionIndex := start }
        (fun _reply => prependRootTransitionSweep (start + 1) count tail) := by
  rfl

/-- Repeat a complete root interval sweep.  Each round starts again at index
zero, which is valid because every request is based on the immutable root. -/
def repeatRootTransitionSweep {Result : Type u} (transitionCount : Nat) :
    (rounds : Nat) → ConcreteRestorationClient Result →
      ConcreteRestorationClient Result
  | 0, tail => tail
  | rounds + 1, tail =>
      prependRootTransitionSweep 0 transitionCount
        (repeatRootTransitionSweep transitionCount rounds tail)

@[simp] theorem repeatRootTransitionSweep_zero
    {Result : Type u} (transitionCount : Nat)
    (tail : ConcreteRestorationClient Result) :
    repeatRootTransitionSweep transitionCount 0 tail = tail := by
  rfl

@[simp] theorem repeatRootTransitionSweep_succ
    {Result : Type u} (transitionCount rounds : Nat)
    (tail : ConcreteRestorationClient Result) :
    repeatRootTransitionSweep transitionCount (rounds + 1) tail =
      prependRootTransitionSweep 0 transitionCount
        (repeatRootTransitionSweep transitionCount rounds tail) := by
  rfl

/-- A reply-branch-independent certificate that a client issues exactly
`count` requests and then returns the named result.  This is a static property
of the extractor program, not a claim that any restoration request succeeds. -/
inductive ExactRequestCount {Result : Type u} (result : Result) :
    Nat → ConcreteRestorationClient Result → Prop where
  | pure : ExactRequestCount result 0 (.pure result)
  | restore (request : ConcreteRestorationRequest)
      (next : ConcreteRestorationReply → ConcreteRestorationClient Result)
      {count : Nat}
      (tails : ∀ reply, ExactRequestCount result count (next reply)) :
      ExactRequestCount result (count + 1) (.restore request next)

theorem prepend_root_transition_sweep_exact_request_count
    {Result : Type u} (result : Result) (start count : Nat) :
    ExactRequestCount result count
      (prependRootTransitionSweep start count (.pure result)) := by
  induction count generalizing start with
  | zero => exact .pure
  | succ count ih =>
      apply ExactRequestCount.restore
      intro reply
      exact ih (start + 1)

/-- Prepending a sweep adds exactly its interval length to any already
certified reply-insensitive client tail. -/
theorem prepend_root_transition_sweep_adds_exact_request_count
    {Result : Type u} {result : Result} {tailCount : Nat}
    {tail : ConcreteRestorationClient Result}
    (tailExact : ExactRequestCount result tailCount tail)
    (start count : Nat) :
    ExactRequestCount result (count + tailCount)
      (prependRootTransitionSweep start count tail) := by
  induction count generalizing start with
  | zero => simpa using tailExact
  | succ count ih =>
      have tails : ∀ (_reply : ConcreteRestorationReply),
          ExactRequestCount result (count + tailCount)
            (prependRootTransitionSweep (start + 1) count tail) := by
        intro reply
        exact ih (start + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ExactRequestCount.restore
          { nodeId := 0, verifierTransitionIndex := start }
          (fun _reply => prependRootTransitionSweep (start + 1) count tail)
          tails)

theorem repeat_root_transition_sweep_exact_request_count
    {Result : Type u} (result : Result) (transitionCount rounds : Nat) :
    ExactRequestCount result (rounds * transitionCount)
      (repeatRootTransitionSweep transitionCount rounds (.pure result)) := by
  induction rounds with
  | zero => simpa using (ExactRequestCount.pure (result := result))
  | succ rounds ih =>
      simpa [Nat.succ_mul, Nat.add_comm] using
        prepend_root_transition_sweep_adds_exact_request_count ih 0
          transitionCount

/-- A root sweep satisfies the operational scheduling rule regardless of its
tail: every generated request names node zero. -/
theorem prepend_root_transition_sweep_replay_base_safe
    {Result : Type u} (start count : Nat)
    (tail : ConcreteRestorationClient Result)
    (tailSafe : ReplayBaseSafeConcreteClient tail) :
    ReplayBaseSafeConcreteClient
      (prependRootTransitionSweep start count tail) := by
  induction count generalizing start with
  | zero => simpa using tailSafe
  | succ count ih =>
      apply ReplayBaseSafeConcreteClient.restore
      · exact root_restoration_request_is_replay_base_safe start
      · intro reply
        exact ih (start + 1)

theorem repeat_root_transition_sweep_replay_base_safe
    {Result : Type u} (transitionCount rounds : Nat)
    (tail : ConcreteRestorationClient Result)
    (tailSafe : ReplayBaseSafeConcreteClient tail) :
    ReplayBaseSafeConcreteClient
      (repeatRootTransitionSweep transitionCount rounds tail) := by
  induction rounds with
  | zero => simpa using tailSafe
  | succ rounds ih =>
      exact prepend_root_transition_sweep_replay_base_safe 0 transitionCount
        _ ih

/-- The production-shaped sweep client: inspect the complete deployed
1513-transition cap for each requested extraction round, then return the fixed
accumulator extractor supplied independently of the hidden tape. -/
def deployedRootSweepClient {Result : Type u} (rounds : Nat)
    (result : Result) : ConcreteRestorationClient Result :=
  repeatRootTransitionSweep 1513 rounds (.pure result)

/-! ## Exact all-reply request coverage -/

/-- One possible request path through an ordinary adaptive client.  Unlike
`ExactRequestCount`, this retains the literal request values. -/
inductive ConcreteRequestPath {Result : Type u} :
    ConcreteRestorationClient Result →
      List ConcreteRestorationRequest → Prop where
  | pure (result : Result) : ConcreteRequestPath (.pure result) []
  | restore
      {request : ConcreteRestorationRequest}
      {next : ConcreteRestorationReply → ConcreteRestorationClient Result}
      (reply : ConcreteRestorationReply)
      {tail : List ConcreteRestorationRequest}
      (tailPath : ConcreteRequestPath (next reply) tail) :
      ConcreteRequestPath (.restore request next) (request :: tail)

/-- Every finite concrete client has at least one request path.  The witness
chooses the fail-closed fuel-exhaustion reply at each branch; no scheduler or
success assumption is involved. -/
theorem concrete_request_path_exists
    {Result : Type u} (client : ConcreteRestorationClient Result) :
    ∃ requests, ConcreteRequestPath client requests := by
  induction client with
  | pure result => exact ⟨[], .pure result⟩
  | restore request next ih =>
      obtain ⟨tail, tailPath⟩ := ih (.failed .restorationFuelExhausted)
      exact ⟨request :: tail, .restore (.failed .restorationFuelExhausted)
        tailPath⟩

/-- Literal request list emitted by one half-open root interval. -/
def rootTransitionRequests : Nat → Nat → List ConcreteRestorationRequest
  | _start, 0 => []
  | start, count + 1 =>
      { nodeId := 0, verifierTransitionIndex := start } ::
        rootTransitionRequests (start + 1) count

/-- Literal request list emitted by repeated complete root sweeps. -/
def repeatedRootTransitionRequests (transitionCount : Nat) :
    Nat → List ConcreteRestorationRequest
  | 0 => []
  | rounds + 1 =>
      rootTransitionRequests 0 transitionCount ++
        repeatedRootTransitionRequests transitionCount rounds

/-- Every request in one half-open root interval names node zero and an
index in that interval.  This small list fact is the basis for selecting the
unique production gamma request in a single deployed sweep. -/
theorem root_transition_request_mem_bounds
    (start count : Nat) (request : ConcreteRestorationRequest)
    (member : request ∈ rootTransitionRequests start count) :
    request.nodeId = 0 ∧ start ≤ request.verifierTransitionIndex ∧
      request.verifierTransitionIndex < start + count := by
  induction count generalizing start with
  | zero => simp [rootTransitionRequests] at member
  | succ count ih =>
      simp only [rootTransitionRequests, List.mem_cons] at member
      rcases member with rfl | later
      · refine ⟨rfl, Nat.le_refl start, ?_⟩
        change start < start + (count + 1)
        omega
      · obtain ⟨node, lower, upper⟩ := ih (start + 1) later
        exact ⟨node, by omega, by omega⟩

/-- A single interval never requests the same root transition twice. -/
theorem root_transition_requests_nodup (start count : Nat) :
    (rootTransitionRequests start count).Nodup := by
  induction count generalizing start with
  | zero => simp [rootTransitionRequests]
  | succ count ih =>
      rw [rootTransitionRequests]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih (start + 1)⟩
      intro member
      obtain ⟨_node, lower, _upper⟩ :=
        root_transition_request_mem_bounds (start + 1) count
          { nodeId := 0, verifierTransitionIndex := start } member
      change start + 1 ≤ start at lower
      omega

/-- The exact request list of one deployed 1513-transition sweep is
duplicate-free.  Repeated sweeps intentionally do not have this property. -/
theorem deployed_root_sweep_one_round_requests_nodup :
    (repeatedRootTransitionRequests 1513 1).Nodup := by
  simpa [repeatedRootTransitionRequests] using
    root_transition_requests_nodup 0 1513

/-- Every adaptive reply path through a prepended interval decomposes into
the fixed literal interval and one genuine path through the supplied tail. -/
theorem prepend_root_transition_sweep_request_path_decompose
    {Result : Type u} {tail : ConcreteRestorationClient Result}
    (start count : Nat) {requests : List ConcreteRestorationRequest}
    (path : ConcreteRequestPath
      (prependRootTransitionSweep start count tail) requests) :
    ∃ tailRequests,
      ConcreteRequestPath tail tailRequests ∧
        requests = rootTransitionRequests start count ++ tailRequests := by
  induction count generalizing start requests with
  | zero =>
      exact ⟨requests, by simpa using path,
        by simp [rootTransitionRequests]⟩
  | succ count ih =>
      rw [prependRootTransitionSweep_succ] at path
      cases path with
      | restore reply nextPath =>
          obtain ⟨tailRequests, tailPath, exact⟩ :=
            ih (start + 1) nextPath
          exact ⟨tailRequests, tailPath, by
            simp only [rootTransitionRequests, List.cons_append]
            rw [exact]⟩

/-- Every adaptive reply path through repeated sweeps is the same repeated
literal root-transition list. -/
theorem repeat_root_transition_sweep_request_path_exact
    {Result : Type u} (transitionCount rounds : Nat) (result : Result)
    {requests : List ConcreteRestorationRequest}
    (path : ConcreteRequestPath
      (repeatRootTransitionSweep transitionCount rounds (.pure result))
      requests) :
    requests = repeatedRootTransitionRequests transitionCount rounds := by
  induction rounds generalizing requests with
  | zero =>
      cases path
      rfl
  | succ rounds ih =>
      rw [repeatRootTransitionSweep_succ] at path
      obtain ⟨tailRequests, tailPath, exact⟩ :=
        prepend_root_transition_sweep_request_path_decompose
          0 transitionCount path
      rw [exact, ih tailPath]
      rfl

/-- Every actual reply path through the production single-round sweep uses
each root transition request exactly once.  This excludes the repeated-request
ambiguity that exists in the generic multi-round extractor. -/
theorem deployed_root_sweep_one_round_path_nodup
    {Result : Type u} (result : Result)
    {requests : List ConcreteRestorationRequest}
    (path : ConcreteRequestPath (deployedRootSweepClient 1 result) requests) :
    requests.Nodup := by
  rw [repeat_root_transition_sweep_request_path_exact 1513 1 result path]
  exact deployed_root_sweep_one_round_requests_nodup

/-- One interval contains every root request whose index is in its half-open
range. -/
theorem root_transition_request_mem
    (start count index : Nat) (lower : start ≤ index)
    (upper : index < start + count) :
    { nodeId := 0, verifierTransitionIndex := index } ∈
      rootTransitionRequests start count := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
      simp only [rootTransitionRequests, List.mem_cons]
      by_cases exact : index = start
      · exact Or.inl (by cases exact; rfl)
      · exact Or.inr (ih (start + 1) (by omega) (by omega))

/-- A nonempty repeated sweep includes every in-range root transition. -/
theorem root_transition_request_mem_repeated
    (transitionCount rounds index : Nat) (roundsPositive : 0 < rounds)
    (indexWithin : index < transitionCount) :
    { nodeId := 0, verifierTransitionIndex := index } ∈
      repeatedRootTransitionRequests transitionCount rounds := by
  cases rounds with
  | zero => omega
  | succ rounds =>
      simp only [repeatedRootTransitionRequests, List.mem_append]
      exact Or.inl (root_transition_request_mem 0 transitionCount index
        (Nat.zero_le index) (by simpa using indexWithin))

/-- Production coverage certificate: on every possible adaptive reply path,
each deployed root transition below 1513 is requested at least once whenever
the extractor asks for a positive number of rounds. -/
theorem deployed_root_sweep_every_path_covers_transition
    {Result : Type u} (rounds : Nat) (result : Result)
    {requests : List ConcreteRestorationRequest}
    (path : ConcreteRequestPath (deployedRootSweepClient rounds result)
      requests)
    (roundsPositive : 0 < rounds) (transitionIndex : Nat)
    (transitionWithin : transitionIndex < 1513) :
    { nodeId := 0, verifierTransitionIndex := transitionIndex } ∈ requests := by
  rw [repeat_root_transition_sweep_request_path_exact 1513 rounds result path]
  exact root_transition_request_mem_repeated 1513 rounds transitionIndex
    roundsPositive transitionWithin

theorem deployed_root_sweep_client_exact_request_count
    {Result : Type u} (rounds : Nat) (result : Result) :
    ExactRequestCount result (rounds * 1513)
      (deployedRootSweepClient rounds result) := by
  exact repeat_root_transition_sweep_exact_request_count result 1513 rounds

theorem deployed_root_sweep_client_replay_base_safe
    {Result : Type u} (rounds : Nat) (result : Result) :
    ReplayBaseSafeConcreteClient (deployedRootSweepClient rounds result) := by
  apply repeat_root_transition_sweep_replay_base_safe
  exact ReplayBaseSafeConcreteClient.pure result

/-! ## Exact fuel closure -/

/-- A single restoration request either leaves the append-only node store
unchanged or appends exactly one child carrying that request as its parent.
Failure records and resource charges do not count as node-store changes. -/
def OneRequestNodeEffect
    {Statement Proof Payload : Type*}
    (before : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (after : ConcreteRestorationAccumulator Statement Proof Payload) : Prop :=
  after.nodes = before.nodes ∨
    ∃ node : ConcreteRestorationNode Statement Proof Payload,
      node.parentRequest = some request ∧
        after.nodes = before.nodes ++ [node]

/-- Parent requests retained by the append-only node store.  The root's
`none` marker is deliberately omitted. -/
def storedParentRequests
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    List ConcreteRestorationRequest :=
  accumulator.nodes.filterMap (fun node => node.parentRequest)

/-- The exact one-request node effect either preserves the retained request
list or appends exactly the request currently being dispatched. -/
theorem one_request_node_effect_stored_parent_requests
    {Statement Proof Payload : Type*}
    {before after : ConcreteRestorationAccumulator Statement Proof Payload}
    {request : ConcreteRestorationRequest}
    (effect : OneRequestNodeEffect before request after) :
    storedParentRequests after = storedParentRequests before ∨
      storedParentRequests after = storedParentRequests before ++ [request] := by
  rcases effect with unchanged | ⟨node, parentExact, appended⟩
  · exact Or.inl (by simp [storedParentRequests, unchanged])
  · exact Or.inr (by
      simp [storedParentRequests, appended, parentExact])

/-- List-level injectivity behind the accumulator-facing theorem below. -/
theorem node_eq_of_same_filter_mapped_parent_request
    {Statement Proof Payload : Type*}
    {nodes : List (ConcreteRestorationNode Statement Proof Payload)}
    (nodup : (nodes.filterMap (fun node => node.parentRequest)).Nodup)
    {left right : ConcreteRestorationNode Statement Proof Payload}
    (leftMem : left ∈ nodes) (rightMem : right ∈ nodes)
    {request : ConcreteRestorationRequest}
    (leftParent : left.parentRequest = some request)
    (rightParent : right.parentRequest = some request) :
    left = right := by
  induction nodes generalizing left right request with
  | nil => simp at leftMem
  | cons head tail ih =>
      cases headParent : head.parentRequest with
      | none =>
          have tailNodup :
              (tail.filterMap (fun node => node.parentRequest)).Nodup := by
            simpa [headParent] using nodup
          simp only [List.mem_cons] at leftMem rightMem
          rcases leftMem with rfl | leftTail
          · rw [headParent] at leftParent
            cases leftParent
          · rcases rightMem with rfl | rightTail
            · rw [headParent] at rightParent
              cases rightParent
            · exact ih tailNodup leftTail rightTail leftParent rightParent
      | some headRequest =>
          have split :
              headRequest ∉ tail.filterMap (fun node => node.parentRequest) ∧
                (tail.filterMap (fun node => node.parentRequest)).Nodup := by
            simpa [headParent] using nodup
          simp only [List.mem_cons] at leftMem rightMem
          rcases leftMem with rfl | leftTail
          · rcases rightMem with rfl | rightTail
            · rfl
            · have requestExact : headRequest = request := by
                rw [headParent] at leftParent
                exact Option.some.inj leftParent
              apply False.elim
              apply split.1
              rw [requestExact]
              exact List.mem_filterMap.mpr
                ⟨right, rightTail, rightParent⟩
          · rcases rightMem with rfl | rightTail
            · have requestExact : headRequest = request := by
                rw [headParent] at rightParent
                exact Option.some.inj rightParent
              apply False.elim
              apply split.1
              rw [requestExact]
              exact List.mem_filterMap.mpr
                ⟨left, leftTail, leftParent⟩
            · exact ih split.2 leftTail rightTail leftParent rightParent

/-- Duplicate-freedom of the stored `some request` keys makes the parent
request an injective identifier for non-root nodes. -/
theorem node_eq_of_same_stored_parent_request
    {Statement Proof Payload : Type*}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    (nodup : (storedParentRequests accumulator).Nodup)
    {left right : ConcreteRestorationNode Statement Proof Payload}
    (leftMem : left ∈ accumulator.nodes)
    (rightMem : right ∈ accumulator.nodes)
    {request : ConcreteRestorationRequest}
    (leftParent : left.parentRequest = some request)
    (rightParent : right.parentRequest = some request) :
    left = right := by
  exact node_eq_of_same_filter_mapped_parent_request nodup leftMem rightMem
    leftParent rightParent

/-- The real one-request dispatcher preserves any terminal property already
proved for every adaptive reply continuation.  This theorem unfolds the
actual preparation, fork, replay and verifier-suffix dispatcher; it does not
replace it by an abstract handler. -/
theorem dispatch_one_concrete_restoration_preserves_all_returned_with_node_effect
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (P : ConcreteRestorationClientRun Statement Proof Payload Result → Prop)
    (continuations : ∀ reply nextAccumulator,
      OneRequestNodeEffect accumulator request nextAccumulator →
        SchedulerNativeCursorAllReturned P (resume reply nextAccumulator)) :
    SchedulerNativeCursorAllReturned P
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  classical
  have failureSafe : ∀
      (failureRequest : ConcreteRestorationRequest)
      (reason : ConcreteRestorationFailure)
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload)
      (nodesExact : nextAccumulator.nodes = accumulator.nodes),
      SchedulerNativeCursorAllReturned P
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nodesExact
    apply continuations _ _
    exact Or.inl (by simpa [ConcreteRestorationAccumulator.addFailure] using
      nodesExact)
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      exact failureSafe request reason _ rfl
  | ready prepared =>
      have preparedRequestExact :=
        AspisK1.V7Tag73ConcreteRestorationTraceInduction.ready_preparation_request_exact
          startProgram configuration accumulator request prepared
            preparationExact
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent :
          HistoryTotalCoherent prepared.programmingBase
      next =>
        simp only [prefixCoherent, if_pos]
        by_cases globalLimit :
            configuration.oracleLimits.totalCalls ≤ globalOracleCalls
        next =>
          simp only [globalLimit, if_pos]
          by_cases pairRoom : prepared.programmingBase.history.length + 2 ≤
              globalOracleCalls
          next =>
            simp only [pairRoom, if_pos]
            intro forkConfiguration
            simp only
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                exact failureSafe prepared.request reason _ rfl
            | ready afterBoth =>
                simp only [programmed]
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  simp only [afterCoherent, if_pos]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    simp only [proverRoom, if_pos]
                    intro proverStage proverFinalOracle proverCoherent
                    cases proverStage with
                    | completed proverResult =>
                        simp only
                        cases proverResult with
                        | error failure =>
                            cases failure with
                            | oracleAbort reason =>
                                exact failureSafe prepared.request
                                  (.proverReplayAbort reason) _ rfl
                            | timeout =>
                                exact failureSafe prepared.request
                                  .proverReplayTimeout _ rfl
                        | ok adversaryValue =>
                            simp only
                            by_cases bindingMismatch :
                                FixedBindings.ofContext
                                    adversaryValue.rawMessages.context ≠
                                  prepared.restoredState.current.bindings
                            next =>
                              rw [dif_pos bindingMismatch]
                              exact failureSafe prepared.request
                                .restoredBindingMismatch _ rfl
                            next =>
                              rw [dif_neg bindingMismatch]
                              by_cases verifierRoom : StageHasOracleRoom
                                  configuration.oracleLimits proverFinalOracle
                                  configuration.verifierFuel
                              next =>
                                simp only [verifierRoom, if_pos]
                                intro verifierStage verifierFinalOracle
                                  verifierCoherent
                                cases verifierStage with
                                | completed verifierResult =>
                                    simp only
                                    cases verifierResult with
                                    | error failure =>
                                        cases failure with
                                        | oracleAbort reason =>
                                            exact failureSafe prepared.request
                                              (.verifierSuffixAbort reason) _ rfl
                                        | timeout =>
                                            exact failureSafe prepared.request
                                              .verifierSuffixTimeout _ rfl
                                    | ok verifierFinalState =>
                                        apply continuations (.added _) _
                                        refine Or.inr ⟨_, ?_, rfl⟩
                                        exact congrArg some preparedRequestExact
                              next =>
                                simp only [verifierRoom, if_neg]
                                exact failureSafe prepared.request
                                  .verifierSuffixRoom _ rfl
                  next =>
                    simp only [proverRoom, if_neg]
                    exact failureSafe prepared.request .proverReplayRoom _ rfl
                next =>
                  simp only [afterCoherent, if_neg]
                  exact failureSafe prepared.request
                    .incoherentProgrammedOracle _ rfl
          next =>
            simp only [pairRoom, if_neg]
            exact failureSafe prepared.request .pairExposureLimit _ rfl
        next =>
          simp only [globalLimit, if_neg]
          exact failureSafe prepared.request .globalLimitTooSmall _ rfl
      next =>
        simp only [prefixCoherent, if_neg]
        exact failureSafe prepared.request .incoherentPrefixOracle _ rfl

/-- Forgetting the exact node-store effect recovers the original terminal
closure theorem. -/
theorem dispatch_one_concrete_restoration_preserves_all_returned
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (P : ConcreteRestorationClientRun Statement Proof Payload Result → Prop)
    (continuations : ∀ reply nextAccumulator,
      SchedulerNativeCursorAllReturned P (resume reply nextAccumulator)) :
    SchedulerNativeCursorAllReturned P
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  apply dispatch_one_concrete_restoration_preserves_all_returned_with_node_effect
    startProgram environment configuration accumulator request resume P
  intro reply nextAccumulator _effect
  exact continuations reply nextAccumulator

/-- If every possible remaining request path is duplicate-free relative to
the parent requests already stored, then every ordinary client result retains
a duplicate-free parent-request store.  This follows the literal fuel-bounded
interpreter and the exact node effect of its dispatcher. -/
theorem concrete_client_preserves_stored_parent_requests_nodup
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (fuel : Nat)
    (client : ConcreteRestorationClient Result)
    (allPathsNodup : ∀ requests, ConcreteRequestPath client requests →
      (storedParentRequests (initialRestorationAccumulatorFromRoot root) ++
        requests).Nodup) :
    SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload Result =>
        (storedParentRequests run.accumulator).Nodup)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration fuel client) := by
  let P := fun run : ConcreteRestorationClientRun Statement Proof Payload
      Result => (storedParentRequests run.accumulator).Nodup
  let motive := fun (_remainingFuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      (∀ requests, ConcreteRequestPath residualClient requests →
        (storedParentRequests accumulator ++ requests).Nodup) →
          SchedulerNativeCursorAllReturned P cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration fuel client motive
      (by
        intro remainingFuel accumulator result pathsNodup
        have exact := pathsNodup [] (.pure result)
        simpa [P] using exact)
      (by
        intro accumulator request next pathsNodup
        obtain ⟨tail, tailPath⟩ :=
          concrete_request_path_exists
            (next (.failed .restorationFuelExhausted))
        have combined := pathsNodup (request :: tail)
          (.restore (.failed .restorationFuelExhausted) tailPath)
        have current : (storedParentRequests accumulator).Nodup :=
          (List.nodup_append.mp combined).1
        simpa [P, storedParentRequests,
          ConcreteRestorationAccumulator.addFailure] using current)
      (by
        intro remainingFuel accumulator request next resume continuations
          pathsNodup
        apply dispatch_one_concrete_restoration_preserves_all_returned_with_node_effect
          startProgram environment configuration accumulator request resume P
        intro reply nextAccumulator effect
        apply continuations reply nextAccumulator
        intro tail tailPath
        have combined := pathsNodup (request :: tail) (.restore reply tailPath)
        rcases one_request_node_effect_stored_parent_requests effect with
          unchanged | appended
        · rw [unchanged]
          exact List.Nodup.sublist
            (List.Sublist.append_left
              (List.Sublist.cons request (List.Sublist.refl tail))
              (storedParentRequests accumulator)) combined
        · rw [appended]
          simpa [List.append_assoc] using combined)
  exact induction allPathsNodup

/-- A single deployed sweep stores at most one child for every literal root
transition request on every ordinary scheduler return. -/
theorem deployed_root_sweep_one_round_stored_parent_requests_nodup
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootIsRoot : root.parentRequest = none)
    (configuration : ConcreteRestorationConfiguration)
    (fuel : Nat) (result : Result) :
    SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload Result =>
        (storedParentRequests run.accumulator).Nodup)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration fuel (deployedRootSweepClient 1 result)) := by
  apply concrete_client_preserves_stored_parent_requests_nodup
    startProgram environment root configuration fuel
      (deployedRootSweepClient 1 result)
  intro requests path
  simpa [storedParentRequests,
    initialRestorationAccumulatorFromRoot, rootIsRoot] using
      deployed_root_sweep_one_round_path_nodup result path

/-- A structurally certified client cannot reach the interpreter's
`restorationFuelExhausted` terminal when its exact request count fits in the
supplied fuel.  This closes the previously external `clientReturned` fact for
all reply-insensitive finite clients, including the deployed root sweep. -/
theorem exact_request_count_prevents_fuel_exhaustion
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (fuel count : Nat)
    (client : ConcreteRestorationClient Result)
    (result : Result)
    (exactCount : ExactRequestCount result count client)
    (fuelEnough : count ≤ fuel) :
    SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload Result =>
        run.halt = .returned result)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration fuel client) := by
  let P := fun run : ConcreteRestorationClientRun Statement Proof Payload
      Result => run.halt = .returned result
  let motive := fun (remainingFuel : Nat)
      (_accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      ∀ residualCount,
        ExactRequestCount result residualCount residualClient →
        residualCount ≤ remainingFuel →
        SchedulerNativeCursorAllReturned P cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration fuel client motive
      (by
        intro remainingFuel accumulator terminalResult residualCount certified
          enough
        cases certified
        rfl)
      (by
        intro accumulator request next residualCount certified enough
        cases certified with
        | restore request next tails => omega)
      (by
        intro remainingFuel accumulator request next resume continuations
          residualCount certified enough
        cases certified with
        | restore certifiedRequest certifiedNext tails =>
            apply dispatch_one_concrete_restoration_preserves_all_returned
              startProgram environment configuration accumulator request resume
              P
            intro reply nextAccumulator
            exact continuations reply nextAccumulator _ (tails reply) (by omega))
  exact induction count exactCount fuelEnough

/-- Production specialization: `rounds * 1513` restoration fuel is sufficient
for the complete deployed root-transition sweep to return its fixed result on
every scheduler branch. -/
theorem deployed_root_sweep_client_returns
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (rounds : Nat) (result : Result) :
    SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload Result =>
        run.halt = .returned result)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration (rounds * 1513)
        (deployedRootSweepClient rounds result)) := by
  apply exact_request_count_prevents_fuel_exhaustion
    startProgram environment root configuration (rounds * 1513)
    (rounds * 1513) (deployedRootSweepClient rounds result) result
  · exact deployed_root_sweep_client_exact_request_count rounds result
  · exact Nat.le_refl _

/-! ## Production configuration and completed-run consequence -/

/-- Replace an arbitrary witness configuration's client by the concrete
deployed root sweep while preserving every machine and replay parameter.
The only new premise is the honest resource inequality demanded by the exact
compiler model. -/
def exactRootSweepWitnessConfiguration
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap) :
    ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity Observation
      Statement Proof Payload Witness parameters where
  machine := base.machine
  restorationConfiguration := base.restorationConfiguration
  restorationFuel := rounds * 1513
  client := deployedRootSweepClient rounds extractor
  bounds :=
    { rootAdversaryTotalCalls := base.bounds.rootAdversaryTotalCalls
      rootAdversaryFreshCalls := base.bounds.rootAdversaryFreshCalls
      rootVerifierTotalCalls := base.bounds.rootVerifierTotalCalls
      replayTotalCalls := base.bounds.replayTotalCalls
      rootAdversaryFuel := base.bounds.rootAdversaryFuel
      rootVerifierFuel := base.bounds.rootVerifierFuel
      replayAdversaryFuel := base.bounds.replayAdversaryFuel
      replayVerifierFuel := base.bounds.replayVerifierFuel
      restorationRequests := withinForkCap }

@[simp] theorem exact_root_sweep_configuration_machine
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap) :
    (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap).machine =
      base.machine := by
  rfl

@[simp] theorem exact_root_sweep_configuration_client
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap) :
    (exactRootSweepWitnessConfiguration base rounds extractor
        withinForkCap).client = deployedRootSweepClient rounds extractor := by
  rfl

/-- Any completed exact compiler run of the production sweep configuration
has returned the fixed extractor.  The conclusion is derived from the actual
cursor terminal and the fuel theorem above; it is no longer a per-sample
`clientReturned` premise. -/
theorem completed_exact_root_sweep_returns_extractor
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload
      (ExactPlainRomWitnessExtractor Statement Proof Payload Witness))
    (completed :
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample).terminal =
        .returned (.completed runtime clientRun)) :
    clientRun.halt = .returned extractor := by
  let configuration := exactRootSweepWitnessConfiguration base rounds extractor
    withinForkCap
  let projection := Classical.choice
    (completed_exact_plain_rom_gives_root_and_store_projection_nonempty
      transitionFuel positive configuration sample runtime clientRun (by
        simpa [configuration] using completed))
  have safe : SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload
          (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
        run.halt = .returned extractor)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment runtime.node
        configuration.restorationConfiguration configuration.restorationFuel
        configuration.client) := by
    change SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload
          (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
        run.halt = .returned extractor)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start sample.1 base.machine.observation)
        base.machine.environment runtime.node base.restorationConfiguration
        (rounds * 1513) (deployedRootSweepClient rounds extractor))
    exact deployed_root_sweep_client_returns
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment runtime.node base.restorationConfiguration
      rounds extractor
  exact run_scheduler_native_list_terminal_respects_all_returned
    (fun run : ConcreteRestorationClientRun Statement Proof Payload
        (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
      run.halt = .returned extractor)
    transitionFuel projection.clientCurrentTransitionFuel _
    projection.rootPrefixes.verifier.remaining clientRun safe
    projection.clientTerminalExact

/-- Direct terminal-equation form of the one-round uniqueness theorem.  This
matches the fixed full-run factorization package used by K1.2--K1.5, whose
returned client result is not the smaller root-only `PUnit` result. -/
theorem returned_one_round_root_sweep_stored_parent_requests_nodup
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel currentTransitionFuel : Nat)
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (answers : List Digest256)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload
      (ExactPlainRomWitnessExtractor Statement Proof Payload Witness))
    (terminalExact :
      runSchedulerNativeListTerminalFrom transitionFuel currentTransitionFuel
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (base.machine.blackBox.start hidden base.machine.observation)
          base.machine.environment runtime.node base.restorationConfiguration
          1513 (deployedRootSweepClient 1 extractor)) answers =
        .returned clientRun) :
    (storedParentRequests clientRun.accumulator).Nodup := by
  have safe :=
    deployed_root_sweep_one_round_stored_parent_requests_nodup
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (base.machine.blackBox.start hidden base.machine.observation)
      base.machine.environment runtime.node rfl base.restorationConfiguration
      1513 extractor
  exact run_scheduler_native_list_terminal_respects_all_returned
    (fun run : ConcreteRestorationClientRun Statement Proof Payload
        (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
      (storedParentRequests run.accumulator).Nodup)
    transitionFuel currentTransitionFuel _ answers clientRun safe terminalExact

/-- In a completed production-shaped one-round sweep, the actual final node
store has an injective non-root parent-request key.  This is the completed-run
form needed to identify a K1.4/K1.5 certificate node with the chronologically
routed gamma child. -/
theorem completed_exact_root_sweep_one_round_stored_parent_requests_nodup
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : 1 * 1513 ≤ parameters.forkRequestCap)
    (sample : ExactCompilerSample HiddenTape parameters)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (clientRun : ConcreteRestorationClientRun Statement Proof Payload
      (ExactPlainRomWitnessExtractor Statement Proof Payload Witness))
    (completed :
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base 1 extractor
            withinForkCap) sample).terminal =
        .returned (.completed runtime clientRun)) :
    (storedParentRequests clientRun.accumulator).Nodup := by
  let configuration := exactRootSweepWitnessConfiguration base 1 extractor
    withinForkCap
  let projection := Classical.choice
    (completed_exact_plain_rom_gives_root_and_store_projection_nonempty
      transitionFuel positive configuration sample runtime clientRun (by
        simpa [configuration] using completed))
  have safe : SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload
          (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
        (storedParentRequests run.accumulator).Nodup)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment runtime.node
        configuration.restorationConfiguration configuration.restorationFuel
        configuration.client) := by
    change SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload
          (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
        (storedParentRequests run.accumulator).Nodup)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start sample.1 base.machine.observation)
        base.machine.environment runtime.node base.restorationConfiguration
        1513 (deployedRootSweepClient 1 extractor))
    exact deployed_root_sweep_one_round_stored_parent_requests_nodup
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment runtime.node rfl base.restorationConfiguration
      1513 extractor
  exact run_scheduler_native_list_terminal_respects_all_returned
    (fun run : ConcreteRestorationClientRun Statement Proof Payload
        (ExactPlainRomWitnessExtractor Statement Proof Payload Witness) =>
      (storedParentRequests run.accumulator).Nodup)
    transitionFuel projection.clientCurrentTransitionFuel _
    projection.rootPrefixes.verifier.remaining clientRun safe
    projection.clientTerminalExact

#print axioms prepend_root_transition_sweep_exact_request_count
#print axioms prepend_root_transition_sweep_adds_exact_request_count
#print axioms repeat_root_transition_sweep_exact_request_count
#print axioms prepend_root_transition_sweep_replay_base_safe
#print axioms repeat_root_transition_sweep_replay_base_safe
#print axioms deployed_root_sweep_client_exact_request_count
#print axioms deployed_root_sweep_client_replay_base_safe
#print axioms root_transition_request_mem_bounds
#print axioms root_transition_requests_nodup
#print axioms deployed_root_sweep_one_round_requests_nodup
#print axioms prepend_root_transition_sweep_request_path_decompose
#print axioms repeat_root_transition_sweep_request_path_exact
#print axioms deployed_root_sweep_one_round_path_nodup
#print axioms root_transition_request_mem_repeated
#print axioms deployed_root_sweep_every_path_covers_transition
#print axioms node_eq_of_same_stored_parent_request
#print axioms dispatch_one_concrete_restoration_preserves_all_returned
#print axioms concrete_client_preserves_stored_parent_requests_nodup
#print axioms deployed_root_sweep_one_round_stored_parent_requests_nodup
#print axioms exact_request_count_prevents_fuel_exhaustion
#print axioms deployed_root_sweep_client_returns
#print axioms exactRootSweepWitnessConfiguration
#print axioms completed_exact_root_sweep_returns_extractor
#print axioms completed_exact_root_sweep_one_round_stored_parent_requests_nodup

end AspisK1.V7Tag73ConcreteRootSweepClient

import AspisFormal.K1.V7Tag73SchedulerProjectedTraceSafety

/-!
# Static must-reach certificates for the scheduler-native interpreter

`SchedulerNativeCursorAllProjectedTracedReturned` proves a property only at
ordinary terminals.  Source alignment also needs a temporal fact: every
successful continuation must pass through a particular pre-answer cursor.

The predicate below is the least proof-relevant tree with exactly that
meaning.  It follows every machine result and every fork coin pair, and it has
no returned or failed constructor.  Consequently it cannot certify a branch
which terminates before reaching the target.  Actual-run extraction from this
static tree is kept separate from its construction by the concrete client.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeMustReach

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult

noncomputable section

universe u

/-- Every scheduler branch which can continue through the represented
machine/fork tree reaches a cursor satisfying `target` before an ordinary
terminal. -/
inductive SchedulerNativeCursorMustReach
    {globalOracleCalls : Nat} {Result : Type u}
    (target : SchedulerNativeCursor globalOracleCalls Result → Prop) :
    SchedulerNativeCursor globalOracleCalls Result → Prop where
  | here (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (holds : target cursor) :
      SchedulerNativeCursorMustReach target cursor
  | machine
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor) (state : OracleState)
      (program : OracleMachine MachineResult) (fuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (onReturned : (result : MachineResult) → (state : OracleState) →
        HistoryTotalCoherent state →
          SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ (result : MachineResult) (finalState : OracleState)
        (finalCoherent : HistoryTotalCoherent finalState),
        SchedulerNativeCursorMustReach target
          (onReturned result finalState finalCoherent)) :
      SchedulerNativeCursorMustReach target
        (.machine limits limitBound actor state program fuel coherent
          onReturned)
  | forkPair
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ scheduled : ScheduledForkCoins,
        scheduled.frozenHistory = frozenHistory →
        scheduled.outputInput = outputInput →
        scheduled.advanceInput = advanceInput →
        scheduled.template = template →
        SchedulerNativeCursorMustReach target (next scheduled.configuration)) :
      SchedulerNativeCursorMustReach target
        (.forkPair frozenHistory pairRoom outputInput advanceInput template next)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ scheduled : ScheduledForkCoins,
        scheduled.frozenHistory = frozenHistory →
        scheduled.outputInput = outputInput →
        scheduled.advanceInput = advanceInput →
        scheduled.template = template →
        scheduled.forkOutput = forkOutput →
        SchedulerNativeCursorMustReach target (next scheduled.configuration)) :
      SchedulerNativeCursorMustReach target
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next)

/-- A stronger stopping predicate can be forgotten pointwise without changing
the operational continuation tree. -/
theorem scheduler_native_must_reach_mono
    {globalOracleCalls : Nat} {Result : Type u}
    {left right : SchedulerNativeCursor globalOracleCalls Result → Prop}
    (imp : ∀ cursor, left cursor → right cursor) :
    ∀ {cursor : SchedulerNativeCursor globalOracleCalls Result},
      SchedulerNativeCursorMustReach left cursor →
        SchedulerNativeCursorMustReach right cursor := by
  intro cursor safe
  induction safe with
  | here cursor holds => exact .here cursor (imp cursor holds)
  | machine limits limitBound actor state program fuel coherent onReturned
      safe ih =>
      exact .machine limits limitBound actor state program fuel coherent
        onReturned (fun result finalState finalCoherent =>
          ih result finalState finalCoherent)
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      exact .forkPair frozenHistory pairRoom outputInput advanceInput template
        next (fun scheduled frozenExact outputExact advanceExact templateExact =>
          ih scheduled frozenExact outputExact advanceExact templateExact)
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      exact .forkAdvance frozenHistory pairRoom outputInput advanceInput
        template forkOutput next
        (fun scheduled frozenExact outputExact advanceExact templateExact
          forkOutputExact =>
          ih scheduled frozenExact outputExact advanceExact templateExact
            forkOutputExact)

#print axioms SchedulerNativeCursorMustReach
#print axioms scheduler_native_must_reach_mono

end
end AspisK1.V7Tag73SchedulerNativeMustReach

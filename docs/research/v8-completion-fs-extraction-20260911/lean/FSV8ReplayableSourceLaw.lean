import FSV8V7CombinedPrehistoryLaw
import ExtractionCollectorReplayableSource

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ReplayableSourceLaw
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7CombinedPrehistoryLaw FSV8V7PrehistoryContinuation
open ExtractionCollectorReplayableSource
open FSV8V7OracleMachineBridge
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := ExtractionCollectorReplayableSource.Point
abbrev Returned := ExtractionCollectorReplayableSource.Returned
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

def replayableCallBound (n m : Nat) : Nat :=
  0 + (0 + 66 + 1 + 66 + 1 + 66 + 1 + 1) +
      (0 + (198 + 1 + 2 * 8 + 1 + 1) + 66 + 1 + 1 + 66 * 3 + 1 + 1 + 1 + 66 * 3 + 1) +
    (1 + 3 * 66 + (1 + m + 594 + 1 + n + 198))

def replayableCurrentLaw {A : Type} (steps : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine A) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) : PMF (CombinedOutcome A Returned) :=
  combinedCurrentLaw steps fallback limits actor preFuel preProgram
    (replayableScript firstWork secondWork producer increment body digest)

def replayableV7Law {A : Type} (steps : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine A) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) : PMF (CombinedOutcome A Returned) :=
  combinedV7Law steps fallback limits actor preFuel preProgram
    (replayableScript firstWork secondWork producer increment body digest)

theorem replayable_current_law_eq_v7_law
    {A : Type} (steps budget : Nat) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (preFuel : Nat)
    (preProgram : OracleMachine A) {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block)
    (scriptFits : replayableCallBound n m ≤ budget)
    (totalBudget : ∀ finiteTape : FreshAnswerTape Block steps,
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.totalCalls +
        budget ≤ limits.totalCalls)
    (freshBudget : ∀ finiteTape : FreshAnswerTape Block steps,
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.freshCalls +
        budget ≤ limits.freshCalls)
    (tapeBudget : ∀ finiteTape : FreshAnswerTape Block steps,
      (prehistoryRun steps limits actor preFuel preProgram finiteTape).oracle.freshCalls +
        budget ≤ steps) :
    replayableCurrentLaw steps fallback limits actor preFuel preProgram
        firstWork secondWork producer increment body digest =
      replayableV7Law steps fallback limits actor preFuel preProgram
        firstWork secondWork producer increment body digest := by
  unfold replayableCurrentLaw replayableV7Law
  apply combined_current_law_eq_v7_law
  intro finiteTape
  have hq : replayableCallBound n m ≤ budget := scriptFits
  refine ⟨?_, ?_, ?_⟩
  · have h := totalBudget finiteTape
    dsimp [replayableScript, replayableCallBound] at hq ⊢
    omega
  · have h := freshBudget finiteTape
    dsimp [replayableScript, replayableCallBound] at hq ⊢
    omega
  · have h := tapeBudget finiteTape
    dsimp [replayableScript, replayableCallBound, projectOracleState] at hq ⊢
    omega

#print axioms replayable_current_law_eq_v7_law
end
end AspisV8Completion.FSV8ReplayableSourceLaw

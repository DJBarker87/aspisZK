import ExtractionCollectorVerifiedSuccessfulMatrix
import SuccessfulReplayAlphaBoundary

/-!
# Actual alpha runs for a complete successful replay family

This leaf adds the source-constructed alpha-run witness pointwise to the
existing complete-matrix family theorem.  It does not identify requested
fork configurations with these actual boundaries and does not assert any
common chronology between matrix cells.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1400

namespace AspisV8Completion.ExtractionCollectorActualAlphaFamily

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorSource
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedMatrix
open ExtractionCollectorSuccessfulReplay
open ExtractionCollectorVerifiedSuccessfulReplay
open ExtractionCollectorVerifiedSuccessfulMatrix
open SuccessfulReplayAlphaBoundary
open FSV8V7OracleMachineBridge
open FSV8ProgrammedProjectionAlignment

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev Tape := FSBoundedTranscript.Tape

theorem complete_constructs_successful_family_with_actual_alpha
    {TapeIdentity Observation Statement Proof : Type*}
    {n m steps : Nat}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Bytes)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : FSBoundedTranscript.RootCuts)
    (initialDigest : Block)
    (finiteTape : FreshAnswerTape Block steps) (tape : Tape)
    (limits : OracleLimits)
    (labels : MatrixLabels K K)
    (outcomes : Outcomes origin firstWork secondWork z cuts initialDigest
      (controllerFromFreshAnswerTape finiteTape) limits (stagedBudget n m))
    (complete : CurrentComplete origin firstWork secondWork z cuts initialDigest
      (controllerFromFreshAnswerTape finiteTape) limits (stagedBudget n m)
      labels outcomes)
    (boundaryFacts : ∀ (row : Fin 29) (column : Fin 4),
      ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin
              (complete.matrix row column).configuration) run},
        constructLegalReplay origin.capability
            (fixedFirstRunRecordFromOrigin origin
              (complete.matrix row column).configuration) = .ok replay →
        ProjectionFacts tape finiteTape replay.val.replayRun.oracle)
    (totalRoom : ∀ (row : Fin 29) (column : Fin 4), ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin
              (complete.matrix row column).configuration) run},
        replay.val.replayRun.oracle.totalCalls + stagedBudget n m ≤
          limits.totalCalls)
    (freshRoom : ∀ (row : Fin 29) (column : Fin 4), ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin
              (complete.matrix row column).configuration) run},
        replay.val.replayRun.oracle.freshCalls + stagedBudget n m ≤
          limits.freshCalls)
    (tapeRoom : ∀ (row : Fin 29) (column : Fin 4), ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin
              (complete.matrix row column).configuration) run},
        (projectOracleState replay.val.replayRun.oracle).next + stagedBudget n m ≤
          steps) :
    ∃ successful : Fin 29 → Fin 4 →
        SuccessfulReplay z cuts initialDigest firstWork secondWork,
      (∀ row column,
        (successful row column).body = (complete.matrix row column).submitted) ∧
      (∀ row column,
        SelectedAccepted.mk (successful row column).body
            (successful row column).record (successful row column).finalDigest =
          (complete.matrix row column).accepted) ∧
      (∀ row column,
        (successful row column).record.gamma = labels.gamma row) ∧
      (∀ row column,
        (successful row column).record.middle.middle.alpha0 =
          labels.alpha row column) ∧
      (∀ row column, ActualAlphaRun (successful row column)) := by
  obtain ⟨successful, bodyEq, acceptedEq, gammaEq, alphaEq⟩ :=
    complete_constructs_successful_family origin firstWork secondWork z cuts
      initialDigest finiteTape tape limits labels outcomes complete boundaryFacts
      totalRoom freshRoom tapeRoom
  refine ⟨successful, bodyEq, acceptedEq, gammaEq, alphaEq, ?_⟩
  intro row column
  exact successful_replay_constructs_actual_alpha_run (successful row column)

#print axioms complete_constructs_successful_family_with_actual_alpha

end
end AspisV8Completion.ExtractionCollectorActualAlphaFamily

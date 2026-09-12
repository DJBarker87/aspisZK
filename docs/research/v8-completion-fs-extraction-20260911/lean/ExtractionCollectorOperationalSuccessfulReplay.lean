import ExtractionCollectorVerifiedSuccessfulReplay

/-!
# Operational provenance for a successful checked replay

This leaf retains the legal replay witness and its constructor equality while
constructing the source-shaped `SuccessfulReplay`.  It adds no semantic,
chronological, or probability premise beyond the existing checked-cell
alignment obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1400

namespace AspisV8Completion.ExtractionCollectorOperationalSuccessfulReplay

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
open FSV8V7OracleMachineBridge
open FSV8ProgrammedProjectionAlignment

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev Tape := FSBoundedTranscript.Tape

abbrev Cell
    {TapeIdentity Observation Statement Proof : Type*}
    {n m steps : Nat}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Bytes)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : FSBoundedTranscript.RootCuts)
    (initialDigest : Block) (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) :=
  CheckedCell origin firstWork secondWork z cuts initialDigest
    (controllerFromFreshAnswerTape finiteTape) limits (stagedBudget n m)

theorem checked_cell_constructs_operational_successfulReplay
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
    (cell : Cell origin firstWork secondWork z cuts initialDigest finiteTape limits)
    (boundaryFacts : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        constructLegalReplay origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) = .ok replay →
        ProjectionFacts tape finiteTape replay.val.replayRun.oracle)
    (totalRoom : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        replay.val.replayRun.oracle.totalCalls + stagedBudget n m ≤
          limits.totalCalls)
    (freshRoom : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        replay.val.replayRun.oracle.freshCalls + stagedBudget n m ≤
          limits.freshCalls)
    (tapeRoom : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        (projectOracleState replay.val.replayRun.oracle).next + stagedBudget n m ≤
          steps) :
    ∃ replay, constructLegalReplay origin.capability
        (fixedFirstRunRecordFromOrigin origin cell.configuration) = .ok replay ∧
      ∃ successful : SuccessfulReplay z cuts initialDigest firstWork secondWork,
        successful.body = cell.submitted ∧
        SelectedAccepted.mk successful.body successful.record
            successful.finalDigest = cell.accepted ∧
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits
            .verifier (stagedBudget n m) replay.val.replayRun.oracle
            (compileScript (wholeStagedScript firstWork secondWork z cuts
              successful.body initialDigest))).halt =
          .returned (.ok successful.record, successful.finalDigest) ∧
        successful.oracle = projectOracleState replay.val.replayRun.oracle := by
  obtain ⟨replay, replayed, returned, output, machineRun, checked, acceptedBody⟩ :=
    cell.constructs_functional_run
  obtain ⟨record, finalDigest, outputEq, acceptedEq⟩ :=
    selectedCheck_accepted_components output cell.accepted checked
  have aligned := run_from_projected_state_aligned limits .verifier
    (wholeStagedScript firstWork secondWork z cuts replay.val.returned initialDigest)
    replay.val.replayRun.oracle (boundaryFacts replay replayed)
    (totalRoom replay) (freshRoom replay) (tapeRoom replay)
  have sourceRun :
      (run tape
        (wholeStagedScript firstWork secondWork z cuts replay.val.returned
          initialDigest)
        (projectOracleState replay.val.replayRun.oracle)).1 = some output := by
    cases sourceResult :
        (run tape
          (wholeStagedScript firstWork secondWork z cuts replay.val.returned
            initialDigest)
          (projectOracleState replay.val.replayRun.oracle)).1 with
    | none =>
        have abortEq :
            (runMachine (controllerFromFreshAnswerTape finiteTape) limits
              .verifier (stagedBudget n m) replay.val.replayRun.oracle
              (compileScript
                (wholeStagedScript firstWork secondWork z cuts
                  replay.val.returned initialDigest))).halt =
              .oracleAbort .controllerRefused := by
          simpa [FSV8V7ProgrammedAlignment.ResultAligned, sourceResult] using
            aligned.1
        have impossible :
            MachineHalt.returned output =
              .oracleAbort .controllerRefused := machineRun.symm.trans abortEq
        cases impossible
    | some result =>
        have returnedEq : result = output := by
          have machineReturned :
              (runMachine (controllerFromFreshAnswerTape finiteTape) limits
                .verifier (stagedBudget n m) replay.val.replayRun.oracle
                (compileScript
                  (wholeStagedScript firstWork secondWork z cuts
                    replay.val.returned initialDigest))).halt =
                .returned result := by
            simpa [FSV8V7ProgrammedAlignment.ResultAligned, sourceResult] using
              aligned.1
          have haltEq : MachineHalt.returned result = .returned output :=
            machineReturned.symm.trans machineRun
          exact MachineHalt.returned.inj haltEq
        simpa [sourceResult, returnedEq]
  have exactSource :
      (run tape
        (wholeStagedScript firstWork secondWork z cuts replay.val.returned
          initialDigest)
        (projectOracleState replay.val.replayRun.oracle)).1 =
          some (.ok record, finalDigest) := by
    simpa [outputEq] using sourceRun
  let successful : SuccessfulReplay z cuts initialDigest firstWork secondWork :=
    { body := replay.val.returned
      tape := tape
      oracle := projectOracleState replay.val.replayRun.oracle
      record := record
      finalDigest := finalDigest
      success := exactSource }
  have machineExact :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits
          .verifier (stagedBudget n m) replay.val.replayRun.oracle
          (compileScript (wholeStagedScript firstWork secondWork z cuts
            successful.body initialDigest))).halt =
        .returned (.ok successful.record, successful.finalDigest) := by
    simpa [successful, outputEq] using machineRun
  exact ⟨replay, replayed, successful, returned, acceptedEq, machineExact, rfl⟩

#print axioms checked_cell_constructs_operational_successfulReplay

end
end AspisV8Completion.ExtractionCollectorOperationalSuccessfulReplay

import ExtractionCollectorVerifiedBodySource
import ExtractionCollectorFinalMatrix

/-!
# Provenance-preserving collection of verified replay attempts

`CompleteMatrix` is deliberately generic, so a matrix over bare parsed records
forgets why any cell was accepted.  This leaf makes the cell itself carry its
origin replay configuration and the equality showing that the operational
`verifiedSourceAttempt` produced it.  The constructor used by
`verifiedAttempt` creates that certificate by dependent matching on the actual
attempt result.

This preserves one-attempt operational and same-body provenance through matrix
selection.  It does not assert that the 116 attempts complete, that their
histories share the correct pre-alpha prefix, or that their finals are valid
folds of one committed object.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1200

namespace AspisV8Completion.ExtractionCollectorVerifiedMatrix

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open ExtractionCollectorSource
open ExtractionCollectorFinalMatrix
open ExtractionCollectorVerifiedBodySource
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8V7OracleMachineBridge

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

variable {TapeIdentity Observation Statement Proof : Type*}
variable {n m : Nat}
variable (origin : SameTapeExperimentOrigin
  TapeIdentity Observation Statement Proof Bytes)
variable (firstWork : Point → Script Bytes Block Unit n)
variable (secondWork : Point → Point → Script Bytes Block Unit m)
variable (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
variable (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)

/-- One selected checked cell, including the exact replay configuration and
the producer equality.  No body, record, or acceptance fact is independently
supplied to later matrix theorems. -/
structure CheckedCell where
  configuration : OriginReplayConfiguration
  submitted : Bytes
  accepted : SelectedAccepted z
  checked : verifiedSourceAttempt origin configuration
      (selectedReplayVerifier firstWork secondWork z cuts initialDigest)
      controller limits fuel = .checked submitted accepted

def CheckedCell.gamma (cell : CheckedCell origin firstWork secondWork z cuts
    initialDigest controller limits fuel) : K :=
  cell.accepted.record.gamma

def CheckedCell.alpha (cell : CheckedCell origin firstWork secondWork z cuts
    initialDigest controller limits fuel) : K :=
  cell.accepted.record.middle.middle.alpha0

def CheckedCell.toReplayRecord
    (cell : CheckedCell origin firstWork secondWork z cuts initialDigest
      controller limits fuel) : ReplayRecord z :=
  ⟨cell.accepted.body, cell.accepted.record⟩

/-- Every checked cell retains the operational replay and same-body functional
run constructed by its actual attempt. -/
theorem CheckedCell.constructs_functional_run
    (cell : CheckedCell origin firstWork secondWork z cuts initialDigest
      controller limits fuel) :
    ∃ replay : {run : CoupledReplay TapeIdentity Statement Proof Bytes //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin cell.configuration) = .ok replay ∧
      replay.val.returned = cell.submitted ∧
      ∃ output,
        (runMachine controller limits .verifier fuel replay.val.replayRun.oracle
          (compileScript (wholeStagedScript firstWork secondWork z cuts
            replay.val.returned initialDigest))).halt = .returned output ∧
        selectedCheck (SelectedVerifierResult.mk replay.val.returned output) =
          .accepted cell.accepted ∧
        cell.accepted.body = cell.submitted :=
  selected_attempt_checked_constructs_functional_run origin cell.configuration
    firstWork secondWork z cuts initialDigest controller limits fuel
    cell.submitted cell.accepted cell.checked

inductive AttemptReject where
  | verifierAbort (reason : OracleAbort)
  | source (reason : SelectedReject)

inductive AttemptResource where
  | verifierTimeout
  | source (reason : SelectedResource)

abbrev Cell := CheckedCell origin firstWork secondWork z cuts initialDigest
  controller limits fuel

/-- Turn one actual configuration into a generic collector outcome while
retaining every operational failure class.  The checked branch constructs the
cell's equality from the dependent match equation itself. -/
def verifiedAttempt (configuration : OriginReplayConfiguration) :
    AttemptOutcome (Cell origin firstWork secondWork z cuts initialDigest
      controller limits fuel) AttemptReject AttemptResource :=
  match result : verifiedSourceAttempt origin configuration
      (selectedReplayVerifier firstWork secondWork z cuts initialDigest)
      controller limits fuel with
  | .replayFailure reason => .replayFailure reason
  | .verifierAbort reason => .rejected (.verifierAbort reason)
  | .verifierTimeout => .resource .verifierTimeout
  | .rejected reason => .rejected (.source reason)
  | .resource reason => .resource (.source reason)
  | .checked submitted accepted => .checked
      { configuration := configuration
        submitted := submitted
        accepted := accepted
        checked := result }

def verifiedAttempts (configurations : List OriginReplayConfiguration)
    (budget : Nat) :
    List (AttemptOutcome (Cell origin firstWork secondWork z cuts initialDigest
      controller limits fuel) AttemptReject AttemptResource) :=
  (configurations.take budget).map
    (verifiedAttempt origin firstWork secondWork z cuts initialDigest controller
      limits fuel)

theorem verified_attempt_count
    (configurations : List OriginReplayConfiguration) (budget : Nat) :
    (verifiedAttempts origin firstWork secondWork z cuts initialDigest controller
      limits fuel configurations budget).length =
      min budget configurations.length := by
  simp [verifiedAttempts]

abbrev Outcomes := List (AttemptOutcome
  (Cell origin firstWork secondWork z cuts initialDigest controller limits fuel)
  AttemptReject AttemptResource)

abbrev CurrentComplete
    (labels : MatrixLabels K K) (outcomes : Outcomes origin firstWork secondWork z
      cuts initialDigest controller limits fuel) :=
  CompleteMatrix
    (CheckedCell.gamma origin firstWork secondWork z cuts initialDigest controller
      limits fuel)
    (CheckedCell.alpha origin firstWork secondWork z cuts initialDigest controller
      limits fuel)
    labels outcomes

/-- Matrix selection no longer erases replay provenance: the selected value is
a `CheckedCell`, so its configuration and exact producer equality remain
available without a list-membership reconstruction. -/
theorem matrix_cell_constructs_functional_run
    (labels : MatrixLabels K K)
    (outcomes : Outcomes origin firstWork secondWork z cuts initialDigest
      controller limits fuel)
    (complete : CurrentComplete origin firstWork secondWork z cuts initialDigest
      controller limits fuel labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    ∃ replay : {run : CoupledReplay TapeIdentity Statement Proof Bytes //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (complete.matrix row column).configuration) run},
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (complete.matrix row column).configuration) = .ok replay ∧
      replay.val.returned = (complete.matrix row column).submitted ∧
      ∃ output,
        (runMachine controller limits .verifier fuel replay.val.replayRun.oracle
          (compileScript (wholeStagedScript firstWork secondWork z cuts
            replay.val.returned initialDigest))).halt = .returned output ∧
        selectedCheck (SelectedVerifierResult.mk replay.val.returned output) =
          .accepted (complete.matrix row column).accepted ∧
        (complete.matrix row column).accepted.body =
          (complete.matrix row column).submitted :=
  (complete.matrix row column).constructs_functional_run

theorem matrix_cell_labels
    (labels : MatrixLabels K K)
    (outcomes : Outcomes origin firstWork secondWork z cuts initialDigest
      controller limits fuel)
    (complete : CurrentComplete origin firstWork secondWork z cuts initialDigest
      controller limits fuel labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    (complete.matrix row column).accepted.record.gamma = labels.gamma row ∧
      (complete.matrix row column).accepted.record.middle.middle.alpha0 =
        labels.alpha row column :=
  ⟨complete.gamma_eq row column, complete.alpha_eq row column⟩

#print axioms CheckedCell.constructs_functional_run
#print axioms verified_attempt_count
#print axioms matrix_cell_constructs_functional_run
#print axioms matrix_cell_labels

end
end AspisV8Completion.ExtractionCollectorVerifiedMatrix

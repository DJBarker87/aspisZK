import ExtractionCollectorInterface

/-!
A source-instantiated shell around the bounded collector interface.  The
experiment, rather than the extractor, closes the actual producer over its
hidden tape by `makeSameTapeExperimentOrigin`.  Every replay then applies one
fixed result checker to the value actually returned by that replay.

This file deliberately does not claim that a checked record is
`RecoveredHigh`, that a requested fork succeeds, or that the progress
predicate below has positive probability.  It is the deterministic collector
half of that future argument only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 300
set_option maxHeartbeats 200000

namespace AspisV8Completion.ExtractionCollectorSource

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
noncomputable section

variable {HiddenTape TapeIdentity Observation Statement Proof Result Record : Type*}
variable {RejectReason ResourceReason Gamma Alpha : Type*}

/-- Result of the actual source checker.  Rejection and checker-side resource
failure are different outcomes and neither is silently converted to `none`. -/
inductive SourceCheckOutcome (Record RejectReason ResourceReason : Type*) where
  | accepted (record : Record)
  | rejected (reason : RejectReason)
  | resource (reason : ResourceReason)

/-- The only checker capability accepted by the collector.  Its input is the
result returned by a legal same-tape replay. -/
structure ActualResultChecker
    (Result Record RejectReason ResourceReason : Type*) where
  check : Result → SourceCheckOutcome Record RejectReason ResourceReason

/-- Experiment-side construction of the origin.  The returned value has no
hidden-tape projection; subsequent collector code receives only this origin. -/
def makeSourceOrigin
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result :=
  makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
    controller limits fuel initialOracle forgeryOf

inductive AttemptOutcome
    (Record RejectReason ResourceReason : Type*) where
  | replayFailure (reason : CouplingFailure)
  | rejected (reason : RejectReason)
  | resource (reason : ResourceReason)
  | checked (record : Record)

/-- One source attempt.  In particular, the checker is applied to
`output.val.returned`, not to a proposed record or requested child id. -/
def sourceAttempt
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration)
    (checker : ActualResultChecker Result Record RejectReason ResourceReason) :
    AttemptOutcome Record RejectReason ResourceReason :=
  match constructLegalReplay origin.capability
      (fixedFirstRunRecordFromOrigin origin configuration) with
  | .error reason => .replayFailure reason
  | .ok output =>
      match checker.check output.val.returned with
      | .accepted record => .checked record
      | .rejected reason => .rejected reason
      | .resource reason => .resource reason

theorem sourceAttempt_checked
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration)
    (checker : ActualResultChecker Result Record RejectReason ResourceReason)
    (record : Record)
    (success : sourceAttempt origin configuration checker = .checked record) :
    ∃ output : {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) run},
      constructLegalReplay origin.capability
        (fixedFirstRunRecordFromOrigin origin configuration) = .ok output ∧
      checker.check output.val.returned = .accepted record := by
  cases replayed : constructLegalReplay origin.capability
      (fixedFirstRunRecordFromOrigin origin configuration) with
  | error reason => simp [sourceAttempt, replayed] at success
  | ok output =>
      cases checked : checker.check output.val.returned with
      | accepted found =>
          have same : found = record := by
            simpa [sourceAttempt, replayed, checked] using success
          exact ⟨output, rfl, same ▸ checked⟩
      | rejected reason => simp [sourceAttempt, replayed, checked] at success
      | resource reason => simp [sourceAttempt, replayed, checked] at success

def sourceAttempts
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configurations : List OriginReplayConfiguration) (budget : Nat)
    (checker : ActualResultChecker Result Record RejectReason ResourceReason) :
    List (AttemptOutcome Record RejectReason ResourceReason) :=
  (configurations.take budget).map fun configuration =>
    sourceAttempt origin configuration checker

theorem source_attempt_count
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configurations : List OriginReplayConfiguration) (budget : Nat)
    (checker : ActualResultChecker Result Record RejectReason ResourceReason) :
    (sourceAttempts origin configurations budget checker).length =
      min budget configurations.length := by
  simp [sourceAttempts]

/-! ## Retained duplicate classification -/

inductive Retained
    (Record RejectReason ResourceReason : Type*) where
  | replayFailure (reason : CouplingFailure)
  | rejected (reason : RejectReason)
  | resource (reason : ResourceReason)
  | checked (record : Record)
  | duplicate (record : Record)

def retainFrom
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha) :
    List (Gamma × Alpha) →
      List (AttemptOutcome Record RejectReason ResourceReason) →
      List (Retained Record RejectReason ResourceReason)
  | _, [] => []
  | seen, .replayFailure reason :: rest =>
      .replayFailure reason :: retainFrom gammaOf alphaOf seen rest
  | seen, .rejected reason :: rest =>
      .rejected reason :: retainFrom gammaOf alphaOf seen rest
  | seen, .resource reason :: rest =>
      .resource reason :: retainFrom gammaOf alphaOf seen rest
  | seen, .checked record :: rest =>
      let label := (gammaOf record, alphaOf record)
      if label ∈ seen then
        .duplicate record :: retainFrom gammaOf alphaOf seen rest
      else
        .checked record :: retainFrom gammaOf alphaOf (label :: seen) rest

def retain
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason)) :
    List (Retained Record RejectReason ResourceReason) :=
  retainFrom gammaOf alphaOf [] outcomes

theorem retainFrom_length
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (seen : List (Gamma × Alpha))
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason)) :
    (retainFrom gammaOf alphaOf seen outcomes).length = outcomes.length := by
  induction outcomes generalizing seen with
  | nil => rfl
  | cons outcome rest ih =>
      cases outcome with
      | replayFailure reason => simp [retainFrom, ih]
      | rejected reason => simp [retainFrom, ih]
      | resource reason => simp [retainFrom, ih]
      | checked record =>
          simp only [retainFrom]
          split <;> simp [ih]

/-! ## Deterministic 29 by 4 completion -/

/-- The requested labels.  Distinctness is data of the schedule, rather than
an inference from having made 116 calls. -/
structure MatrixLabels (Gamma Alpha : Type*) where
  gamma : Fin 29 → Gamma
  alpha : Fin 29 → Fin 4 → Alpha
  gamma_injective : Function.Injective gamma
  alpha_injective : ∀ row, Function.Injective (alpha row)

def findChecked
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason))
    (gamma : Gamma) (alpha : Alpha) : Option Record :=
  outcomes.findSome? fun outcome =>
    match outcome with
    | .checked record =>
        if gammaOf record = gamma ∧ alphaOf record = alpha then some record else none
    | _ => none

/-- This is the exact deterministic progress condition: every scheduled cell
has already produced a checker-accepted record.  No probability or
`RecoveredHigh` predicate occurs in it. -/
def Progress
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason)) : Prop :=
  ∀ row column,
    (findChecked gammaOf alphaOf outcomes (labels.gamma row)
      (labels.alpha row column)).isSome

theorem findChecked_labels
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason))
    (gamma : Gamma) (alpha : Alpha) (record : Record)
    (found : findChecked gammaOf alphaOf outcomes gamma alpha = some record) :
    gammaOf record = gamma ∧ alphaOf record = alpha := by
  induction outcomes with
  | nil => simp [findChecked] at found
  | cons outcome rest ih =>
      cases outcome with
      | replayFailure reason => exact ih found
      | rejected reason => exact ih found
      | resource reason => exact ih found
      | checked candidate =>
          simp only [findChecked, List.findSome?_cons] at found
          by_cases hit : gammaOf candidate = gamma ∧ alphaOf candidate = alpha
          · simp [hit] at found
            subst record
            exact hit
          · simp [hit] at found
            exact ih found

structure CompleteMatrix
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason)) where
  matrix : Fin 29 → Fin 4 → Record
  selected : ∀ row column,
    findChecked gammaOf alphaOf outcomes (labels.gamma row)
      (labels.alpha row column) = some (matrix row column)
  gamma_eq : ∀ row column, gammaOf (matrix row column) = labels.gamma row
  alpha_eq : ∀ row column, alphaOf (matrix row column) = labels.alpha row column

def completeMatrix
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason))
    (progress : Progress gammaOf alphaOf labels outcomes) :
    CompleteMatrix gammaOf alphaOf labels outcomes := by
  let matrix : Fin 29 → Fin 4 → Record := fun row column =>
    (findChecked gammaOf alphaOf outcomes (labels.gamma row)
      (labels.alpha row column)).get (progress row column)
  have selected : ∀ row column,
      findChecked gammaOf alphaOf outcomes (labels.gamma row)
        (labels.alpha row column) = some (matrix row column) := fun row column =>
    (Option.some_get (progress row column)).symm
  exact
    { matrix := matrix
      selected := selected
      gamma_eq := fun row column =>
        (findChecked_labels gammaOf alphaOf outcomes _ _ _ (selected row column)).1
      alpha_eq := fun row column =>
        (findChecked_labels gammaOf alphaOf outcomes _ _ _ (selected row column)).2 }

inductive CollectorResult
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason)) where
  | incomplete
      (retained : List (Retained Record RejectReason ResourceReason))
  | complete
      (matrix : CompleteMatrix gammaOf alphaOf labels outcomes)
      (retained : List (Retained Record RejectReason ResourceReason))

def collect29x4
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason)) :
    CollectorResult gammaOf alphaOf labels outcomes := by
  classical
  exact if progress : Progress gammaOf alphaOf labels outcomes then
      .complete (completeMatrix gammaOf alphaOf labels outcomes progress)
        (retain gammaOf alphaOf outcomes)
    else
      .incomplete (retain gammaOf alphaOf outcomes)

theorem progress_implies_complete
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason))
    (progress : Progress gammaOf alphaOf labels outcomes) :
    ∃ matrix retained,
      collect29x4 gammaOf alphaOf labels outcomes = .complete matrix retained := by
  classical
  unfold collect29x4
  split
  next established =>
    exact ⟨completeMatrix gammaOf alphaOf labels outcomes established,
      retain gammaOf alphaOf outcomes, rfl⟩
  next absent => exact (absent progress).elim

theorem complete_gamma_distinct
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes) :
    ∀ {row₁ row₂ : Fin 29}, row₁ ≠ row₂ →
      gammaOf (complete.matrix row₁ 0) ≠ gammaOf (complete.matrix row₂ 0) := by
  intro row₁ row₂ different same
  apply different
  apply labels.gamma_injective
  exact (complete.gamma_eq row₁ 0).symm.trans
    (same.trans (complete.gamma_eq row₂ 0))

theorem complete_alpha_distinct
    [DecidableEq Gamma] [DecidableEq Alpha]
    (gammaOf : Record → Gamma) (alphaOf : Record → Alpha)
    (labels : MatrixLabels Gamma Alpha)
    (outcomes : List (AttemptOutcome Record RejectReason ResourceReason))
    (complete : CompleteMatrix gammaOf alphaOf labels outcomes) :
    ∀ row {column₁ column₂ : Fin 4}, column₁ ≠ column₂ →
      alphaOf (complete.matrix row column₁) ≠
        alphaOf (complete.matrix row column₂) := by
  intro row column₁ column₂ different same
  apply different
  apply labels.alpha_injective row
  exact (complete.alpha_eq row column₁).symm.trans
    (same.trans (complete.alpha_eq row column₂))

#print axioms sourceAttempt_checked
#print axioms source_attempt_count
#print axioms retainFrom_length
#print axioms progress_implies_complete
#print axioms complete_gamma_distinct
#print axioms complete_alpha_distinct

end
end AspisV8Completion.ExtractionCollectorSource

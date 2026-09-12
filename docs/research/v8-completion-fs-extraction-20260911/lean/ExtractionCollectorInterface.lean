import AspisFormal.K1.V7FsStateRestorationCoupling

/-! Bounded checked-record collection from the exact V7 same-origin replay
constructor. A normally returned replay is NOT acceptance. The separate
result checker is evaluated, and rejection is retained. Instantiating that
checker with the selected source verifier, constructing nested origins, and
classifying selected records as recovered/middle remain explicit seams.
No successful-fork, candidate-inclusion, or probability premise is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000

namespace AspisV8Completion.ExtractionCollectorInterface
open AspisK1.V7FsStateRestorationCoupling
noncomputable section

variable {TapeIdentity Observation Statement Proof Result Record : Type*}

inductive Failure where
  | replay (reason : CouplingFailure)
  | resultRejected

/-- The checker receives an actually returned result, never a proposed
candidate, a supplied family member, or an `added` node identifier. Its
successful output is only a checked record until a source refinement proves
what that checker enforces. -/
def attempt
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration)
    (check : Result → Option Record) : Except Failure Record :=
  match constructLegalReplay origin.capability
      (fixedFirstRunRecordFromOrigin origin configuration) with
  | .error reason => .error (.replay reason)
  | .ok output =>
      match check output.val.returned with
      | none => .error .resultRejected
      | some record => .ok record

/-- Actual execution and actual checker success are derived from the
constructor result. Operational replay legality is the existing V7 payload;
it does not assert selected verifier acceptance or successful extraction. -/
theorem attempt_success
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration)
    (check : Result → Option Record) (record : Record)
    (success : attempt origin configuration check = .ok record) :
    ∃ output : {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) run},
      constructLegalReplay origin.capability
        (fixedFirstRunRecordFromOrigin origin configuration) = .ok output ∧
      check output.val.returned = some record := by
  cases replayed : constructLegalReplay origin.capability
      (fixedFirstRunRecordFromOrigin origin configuration) with
  | error reason => simp [attempt, replayed] at success
  | ok output =>
      cases checked : check output.val.returned with
      | none => simp [attempt, replayed, checked] at success
      | some found =>
          have same : found = record := by
            simpa [attempt, replayed, checked] using success
          exact ⟨output, rfl, same ▸ checked⟩

/-- Every requested attempt has a retained outcome, including all failures.
The origin is fixed; configurations cannot replace its observation, first
execution, initial oracle or hidden-tape start capability. -/
def attempts
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configurations : List OriginReplayConfiguration) (budget : Nat)
    (check : Result → Option Record) : List (Except Failure Record) :=
  (configurations.take budget).map fun configuration => attempt origin configuration check

def checkedRecords
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configurations : List OriginReplayConfiguration) (budget : Nat)
    (check : Result → Option Record) : List Record :=
  (attempts origin configurations budget check).filterMap Except.toOption

theorem attempt_count
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configurations : List OriginReplayConfiguration) (budget : Nat)
    (check : Result → Option Record) :
    (attempts origin configurations budget check).length = min budget configurations.length := by
  simp only [attempts, List.length_map, List.length_take]

theorem checked_count
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (configurations : List OriginReplayConfiguration) (budget : Nat)
    (check : Result → Option Record) :
    (checkedRecords origin configurations budget check).length ≤ budget := by
  have filtered := List.length_filterMap_le (f := Except.toOption)
    (attempts origin configurations budget check)
  rw [attempt_count] at filtered
  exact filtered.trans (Nat.min_le_left _ _)

/-- Shape only: neither this count nor a replay return supplies 116 accepted
or recovered records. Distinct gamma/alpha labels must still be checked. -/
theorem required_matrix_size : Fintype.card (Fin 29 × Fin 4) = 116 := by
  norm_num

#print axioms attempt_success
#print axioms attempt_count
#print axioms checked_count
#print axioms required_matrix_size
end
end AspisV8Completion.ExtractionCollectorInterface

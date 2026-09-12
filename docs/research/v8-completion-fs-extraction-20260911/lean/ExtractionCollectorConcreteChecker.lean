import ExtractionCollectorSource
import SameBodyRelation

/-!
The strongest collector checker that can be instantiated from the current
same-body relation return type. `SameBodyRelation.consume` returns
`Option (SameBodyRelation.Result K)`: `none` is the actual consistency-check
rejection and `some result` contains the three computed result fields.

The selected Merkle slice has a separate return type
`Option (Schedule × Option OrderedRawQueryLog) × Oracle`; it is not integrated
with this relation result. Neither current return contains the submitted
body, gamma, and alpha together, so neither can label a 29 by 4 collector
record without taking those values from outside the returned result.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 300
set_option maxHeartbeats 200000

namespace AspisV8Completion.ExtractionCollectorConcreteChecker

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open ExtractionCollectorSource
open SameBodyRelation
noncomputable section

universe u v
variable {K : Type u} {Schedule : Type v}

/-- Literal return type of the current same-body consistency checker. -/
abbrev CurrentSameBodyResult (K : Type u) := Option (SameBodyRelation.Result K)

/-- No proposed candidate or analysis predicate is added: the checked record
is exactly the result constructed by `SameBodyRelation.consume`. -/
abbrev CheckedSameBodyRecord (K : Type u) := SameBodyRelation.Result K

inductive SameBodyRejectReason where
  | consistencyRejected
  deriving DecidableEq, Repr

/-- `consume` has no separate resource branch. The empty type prevents the
checker from inventing one. Replay-level resource failures remain in
`AttemptOutcome.replayFailure`. -/
abbrev SameBodyResourceReason := Empty

def checkCurrentSameBody
    (returned : CurrentSameBodyResult K) :
    SourceCheckOutcome (CheckedSameBodyRecord K) SameBodyRejectReason
      SameBodyResourceReason :=
  match returned with
  | none => .rejected .consistencyRejected
  | some result => .accepted result

def currentSameBodyChecker :
    ActualResultChecker (CurrentSameBodyResult K) (CheckedSameBodyRecord K)
      SameBodyRejectReason SameBodyResourceReason where
  check := checkCurrentSameBody

/-- The checker cannot substitute a supplied record: success says the replay
returned that exact `SameBodyRelation.Result`. -/
theorem checkCurrentSameBody_accepted
    (returned : CurrentSameBodyResult K) (record : CheckedSameBodyRecord K)
    (accepted : checkCurrentSameBody returned = .accepted record) :
    returned = some record := by
  cases returned with
  | none => simp [checkCurrentSameBody] at accepted
  | some result =>
      have same : result = record := by
        simpa [checkCurrentSameBody] using accepted
      exact congrArg some same

/-- One useful checked-output property: all 256 final values in the record are
the literal final vector returned by `consume`, not checker inputs. -/
theorem accepted_final_is_returned
    (returned : CurrentSameBodyResult K) (record : CheckedSameBodyRecord K)
    (accepted : checkCurrentSameBody returned = .accepted record) :
    ∃ actual, returned = some actual ∧
      ∀ index, actual.final256 index = record.final256 index := by
  exact ⟨record, checkCurrentSameBody_accepted returned record accepted,
    fun _ => rfl⟩

/-! ## Current producer instantiation and exact replay obstruction -/

/-- All public inputs currently consumed by the pure relation checker. The
causal strategy is kept as the hidden same-tape producer state. -/
structure CurrentSameBodyObservation (K : Type u) (Schedule : Type v) where
  ops : SameBodyRelation.Arithmetic K
  word : Word K
  tau : K
  alpha0 : K
  queries : Schedule
  rho : K
  laterCoins : Fin 3 → K
  ordinary : K
  increment : Final K → Schedule → K → K

def currentSameBodyBlackBox [DecidableEq K] :
    SameTapeBlackBox (Strategy K Schedule) (CurrentSameBodyObservation K Schedule)
      (CurrentSameBodyResult K) where
  start strategy observation :=
    .pure (consume observation.ops strategy observation.word observation.tau
      observation.alpha0 observation.queries observation.rho
      observation.laterCoins observation.ordinary observation.increment)

def makeCurrentSameBodyOrigin
    [DecidableEq K] {TapeIdentity Statement Proof : Type*}
    (strategy : Strategy K Schedule) (identity : TapeIdentity)
    (observation : CurrentSameBodyObservation K Schedule)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : CurrentSameBodyResult K → Option (PublicProof Statement Proof)) :
    SameTapeExperimentOrigin TapeIdentity (CurrentSameBodyObservation K Schedule)
      Statement Proof (CurrentSameBodyResult K) :=
  makeSourceOrigin currentSameBodyBlackBox strategy identity observation
    controller limits fuel initialOracle forgeryOf

/-- Exact typed obstruction: the current same-body producer evaluates its
functional checker before returning a pure V7 oracle machine. Hence the V7
restoration constructor has no query in this program at which to pause and
program gamma or alpha. -/
theorem current_origin_start_is_pure
    [DecidableEq K] {TapeIdentity Statement Proof : Type*}
    (strategy : Strategy K Schedule) (identity : TapeIdentity)
    (observation : CurrentSameBodyObservation K Schedule)
    (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)
    (initialOracle : OracleState)
    (forgeryOf : CurrentSameBodyResult K → Option (PublicProof Statement Proof)) :
    (makeCurrentSameBodyOrigin strategy identity observation controller limits fuel
      initialOracle forgeryOf).capability.start observation =
      .pure (consume observation.ops strategy observation.word observation.tau
        observation.alpha0 observation.queries observation.rho
        observation.laterCoins observation.ordinary observation.increment) := by
  rfl

/-- Minimal runtime return shape required by the existing 29 by 4 collector.
The source must construct these fields in the same causal execution. Merely
closing this structure over checker arguments would violate the access
contract. Body/authentication provenance remains a subsequent source
refinement theorem, rather than an unverified proof field. -/
structure ReplayableLabelledSameBodyResult
    (Gamma Alpha Body : Type*) (K : Type u) where
  gamma : Gamma
  alpha : Alpha
  body : Body
  checked : SameBodyRelation.Result K

def ReplayableLabelledSameBodyResult.record
    {Gamma Alpha Body : Type*} {K : Type u}
    (returned : ReplayableLabelledSameBodyResult Gamma Alpha Body K) :
    CheckedSameBodyRecord K :=
  returned.checked

theorem labelled_record_is_returned
    {Gamma Alpha Body : Type*} {K : Type u}
    (returned : ReplayableLabelledSameBodyResult Gamma Alpha Body K) :
    returned.record = returned.checked := by
  rfl

#print axioms checkCurrentSameBody_accepted
#print axioms accepted_final_is_returned
#print axioms current_origin_start_is_pure
#print axioms labelled_record_is_returned

end
end AspisV8Completion.ExtractionCollectorConcreteChecker

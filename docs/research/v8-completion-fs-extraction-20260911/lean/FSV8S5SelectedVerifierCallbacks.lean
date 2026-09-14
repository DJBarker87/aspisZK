import FSV8ExactRootCursor
import FSV8BeforeAlphaMarkerFactorization
import FSV8FreshTapeBudget

/-!
Selected read-only OOD callbacks for the structured verifier suffix beginning
after the point claims.  `inactive_row_binding::to_gamma` reads proof-carried
rows; it does not run a hash-capable answer prover.  The `answerScript`
wrapper, rather than the zero-work callback itself, emits the exact canonical
same-body OOD payload before its transcript absorb.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800
namespace AspisV8Completion.FSV8S5SelectedVerifierCallbacks
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8OODBodyScript FSV8PostOODGammaScript FSV8FreshTapeBudget
open FSV8BeforeAlphaMarkerFactorization
open FSV8ExactRootCursor
open AspisK1.V7Tag73ExactCompilerResources

abbrev Bytes := List UInt8
abbrev HB := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

def sourceReadOnlyFirst (_ : Point) : Script Bytes HB Unit 0 := .done ()
def sourceReadOnlySecond (_ _ : Point) : Script Bytes HB Unit 0 := .done ()

@[simp] theorem run_sourceReadOnlyFirst (point : Point)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle) :
    run tape (sourceReadOnlyFirst point) oracle = (some (), oracle) := rfl

@[simp] theorem run_sourceReadOnlySecond (first second : Point)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle) :
    run tape (sourceReadOnlySecond first second) oracle = (some (), oracle) := rfl

/-- The actual source has no callback work at this point, but `answerScript`
still produces the canonical row from this same body.  Thus the no-op preserves
the persistent oracle while the enclosing script absorbs the source payload. -/
theorem source_readOnly_answer_script_exact (point : Point) (body : Bytes)
    (sample : Fin 2) (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle) :
    run tape (answerScript sourceReadOnlyFirst point body sample) oracle =
      (some (answerBytes body sample), oracle) := by
  simp [answerScript, sourceReadOnlyFirst, FSTranscriptScript.map, FSOracleExecution.run]

/-- An explicit experiment constructor, not a claim that all Configurations
are equivalent. It preserves the common inputs and selects the literal
same-body read-only OOD payload path plus the named adversary resource bound.
It still does not construct the outer selected configuration from Rust. -/
def selectedConfiguration
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters) {n m : Nat}
    (base : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m) :
    Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) 0 0 where
  blackBox := base.blackBox
  tapeIdentity := base.tapeIdentity
  observation := base.observation
  adversaryLimits := base.adversaryLimits
  verifierLimits := base.verifierLimits
  adversaryFuel := parameters.q1ShaCallCap
  firstWork := sourceReadOnlyFirst
  secondWork := sourceReadOnlySecond
  z := base.z
  cuts := base.cuts
  initialDigest := base.initialDigest
  adversaryLimitBound := base.adversaryLimitBound
  verifierLimitBound := base.verifierLimitBound

@[simp] theorem selected_adversary_fuel
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters) {n m : Nat}
    (base : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m) :
    (selectedConfiguration parameters base).adversaryFuel =
      parameters.q1ShaCallCap := rfl

/-- The dependent boundary is returned by the actual prefix, not assembled
from independently selected OOD/gamma/body records. -/
structure SelectedBeforeMarker (body : Bytes) (z : Fin 10 → K) where
  out : OODResult
  gamma : K
  boundary : BeforeAlphaMarker out gamma body z

abbrev SelectedPrefixError :=
  Sum (Sum FSOODSampler.Error FSNonzeroQM31.Error)
    FSLiveSourceFunctionalMiddle.Error

def selectedBeforeMarkerScript (body : Bytes) (z : Fin 10 → K) (digest : HB) :
    Script Bytes HB
      (Except SelectedPrefixError (SelectedBeforeMarker body z) × HB) 1394 :=
  bind (m := 401)
      (sourceThenGammaScript sourceReadOnlyFirst sourceReadOnlySecond body digest)
    fun source =>
      match source.1 with
      | .error error => .done (.error (.inl error), source.2)
      | .ok pair =>
          map (fun result =>
            (match result.1 with
              | .error error => Except.error (Sum.inr error)
              | .ok boundary => Except.ok
                  ({ out := pair.1, gamma := pair.2, boundary := boundary } :
                    SelectedBeforeMarker body z), result.2))
            (beforeAlphaMarkerScript pair.1 pair.2 body z source.2)

/-- This 1394 cap follows from actual Script syntax, for arbitrary initial
cache/history and for rejection as well as success. -/
theorem selected_before_marker_call_bound (body : Bytes) (z : Fin 10 → K)
    (digest : HB) (tape : FSBoundedTranscript.Tape)
    (oracle : FSBoundedTranscript.Oracle) :
    (run tape (selectedBeforeMarkerScript body z digest) oracle).2.log.length ≤
      oracle.log.length + 1394 :=
  call_bound tape _ _

@[simp] theorem selected_source_budget : sourceThenGammaBudget 0 0 = 993 := rfl

#print axioms source_readOnly_answer_script_exact
#print axioms selected_adversary_fuel
#print axioms selected_before_marker_call_bound
end
end AspisV8Completion.FSV8S5SelectedVerifierCallbacks

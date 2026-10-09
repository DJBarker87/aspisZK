import FSLiveSemanticPrefix
import FSV8S4VerifierOnlySuffix

/-!
# Dynamic same-body selected root (guard-relaxed)

This module removes the old `Configuration.z`, `initialDigest`, and `RootCuts`
inputs from the functional verifier program.  The semantic execution parses the
submitted body and produces `z` and its final digest.  The selected suffix then
uses exactly those values.  Its operational Merkle roots are parsed from the
same body.

The remaining fields of `RootCuts` are chronology witnesses used by later
authentication arguments; `selected22` reads only `c1` and `c2`.  They are
therefore filled with inert values here and are deliberately not exported as
authenticated cuts.  Constructing the real chronological cuts is a separate
probability/extraction obligation.

This is the guard-relaxed source root: `FSLiveSemanticPrefix.semanticScript`
does not execute the selected semantic terminal.  Consequently no theorem in
this file claims literal verifier acceptance or Rust refinement.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8S7DynamicSelectedRoot

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveSemanticPrefix SameBodySemanticWire
open FSV8S4VerifierOnlySuffix
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ExactCompilerResources

noncomputable section

abbrev Bytes := List UInt8
abbrev K := FSNonzeroQM31.K
abbrev B := FSBoundedTranscript.Block

/-- An inert value for the analysis-only cut fields.  It is not claimed to be
the chronological C1 or C2 cut of an execution. -/
def inertOracle : FSBoundedTranscript.Oracle where
  cache := fun _ => none
  next := 0
  log := []

def inertTranscript : FSBoundedTranscript.Transcript where
  digest := zeroDigest
  oracle := inertOracle

/-- Operational cut projection used by the selected Merkle verifier.  Both
roots are obtained from the same successful canonical parse of `body`; there
is no independent root input. -/
def operationalCuts (wire : SameBodySemanticWire.Wire) : RootCuts where
  c1 := wire.roots 0
  c2 := wire.roots 1
  c1Cut := inertOracle
  c2Cut := inertOracle
  final := inertTranscript
  lambda := []
  chi := []

def cutsFromBody (body : Bytes) : Option RootCuts :=
  (SameBodySemanticWire.parse body).map operationalCuts

structure RelaxedSuccess (body : Bytes) where
  semantic : FSLiveSemanticPrefix.Success
  record : FSAuthenticatedInterleavedPrefixMiddle.Record body semantic.z
  finalDigest : B

inductive Error where
  | semantic (error : FSLiveSemanticPrefix.Error)
  | bodyAfterSemantic
  | suffix (error : FSAuthenticatedInterleavedPrefixMiddle.Error)

abbrev suffixBudget : Nat := 1 + stagedBudget 0 0
abbrev verifierBudget : Nat := 1800 + suffixBudget

/-- One dynamically indexed verifier program.  `z`, the semantic digest and
the roots consumed by the Merkle suffix are all constructed from this run and
this body. -/
def verifierScript (positiveTransfer : Bool) (binding : Binding)
    (body : Bytes) :
    Script Bytes B (Except Error (RelaxedSuccess body) × B) verifierBudget :=
  bind (m := suffixBudget) (semanticScript positiveTransfer binding body) fun semantic =>
    match semantic with
    | .error error => .done (.error (.semantic error), zeroDigest)
    | .ok state =>
      match cutsFromBody body with
      | none => .done (.error .bodyAfterSemantic, state.finalDigest)
      | some cuts =>
        FSTranscriptScript.map
          (fun suffix =>
            (match suffix.1 with
              | .error error => Except.error (.suffix error)
              | .ok record => Except.ok
                  { semantic := state
                    record := record
                    finalDigest := suffix.2 },
             suffix.2))
          (selectedSuffixBeforePoints state.z cuts body state.finalDigest)

/-- The inspected research profile enables the positive-transfer semantic
adapter.  The structured/dense choice is arithmetic-only after the common
functional relation and is outside this transcript program. -/
def selectedVerifierScript (binding : Binding) (body : Bytes) :=
  verifierScript true binding body

/-- Successful execution exposes the semantic state that actually indexes the
selected record.  No equality to caller-provided `z` or digest is present. -/
theorem successful_run_constructs_dynamic_context
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : Oracle)
    (accepted : RelaxedSuccess body) (digest : B)
    (success : (run tape (verifierScript positiveTransfer binding body) oracle).1 =
      some (.ok accepted, digest)) :
    accepted.finalDigest = digest ∧
      ∃ wire, SameBodySemanticWire.parse body = some wire := by
  unfold verifierScript at success
  rw [run_bind] at success
  cases semanticRun : (run tape (semanticScript positiveTransfer binding body) oracle).1 with
  | none => simp [semanticRun] at success
  | some semantic =>
    cases semantic with
    | error error => simp [semanticRun, FSOracleExecution.run] at success
    | ok state =>
      cases parsed : SameBodySemanticWire.parse body with
      | none => simp [semanticRun, cutsFromBody, parsed, FSOracleExecution.run] at success
      | some wire =>
        simp only [semanticRun, cutsFromBody, parsed, Option.map_some] at success
        rw [run_map] at success
        cases suffixRun :
            (run tape
              (selectedSuffixBeforePoints state.z (operationalCuts wire) body
                state.finalDigest)
              (run tape (semanticScript positiveTransfer binding body) oracle).2).1 with
        | none => simp [suffixRun] at success
        | some suffix =>
          rcases suffix with ⟨result, finalDigest⟩
          cases result with
          | error error => simp [suffixRun] at success
          | ok record =>
            simp [suffixRun] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨rfl, wire, rfl⟩

/-- The dynamically produced semantic state also comes from a successful
same-body canonical parse; this is inherited from the executed semantic
program, rather than supplied as an alignment premise. -/
theorem successful_run_has_canonical_wire
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : Oracle)
    (accepted : RelaxedSuccess body) (digest : B)
    (success : (run tape (verifierScript positiveTransfer binding body) oracle).1 =
      some (.ok accepted, digest)) :
    ∃ wire, SameBodySemanticWire.parse body = some wire ∧
      AspisV8.SameBodySequentialCodec.fields (body.map UInt8.toFin) =
        some wire.values := by
  obtain ⟨_, ⟨wire, parsed⟩⟩ :=
    successful_run_constructs_dynamic_context positiveTransfer binding body tape
      oracle accepted digest success
  exact ⟨wire, parsed, SameBodySemanticWire.fields_exact body wire parsed⟩

/-- Root inputs fixed before the master random-oracle tape.  In contrast with
`FSV8ExactRootCursor.Configuration`, this contains no semantic `z`, digest or
cut record. -/
structure DynamicConfiguration
    (HiddenTape TapeIdentity Observation : Type)
    (globalOracleCalls : Nat) where
  blackBox : SameTapeBlackBox HiddenTape Observation Bytes
  tapeIdentity : HiddenTape → TapeIdentity
  observation : Observation
  adversaryLimits : OracleLimits
  verifierLimits : OracleLimits
  adversaryFuel : Nat
  binding : Binding
  adversaryLimitBound : adversaryLimits.totalCalls ≤ globalOracleCalls
  verifierLimitBound : verifierLimits.totalCalls ≤ globalOracleCalls

/-- Result returned by the nested native callbacks.  `output` is indexed by
the exact body returned by this adversary invocation. -/
structure Runtime (TapeIdentity : Type) where
  tapeIdentity : TapeIdentity
  body : Bytes
  proverFinalOracle : OracleState
  verifierFinalOracle : OracleState
  output : Except Error (RelaxedSuccess body) × B

/-- Acceptance is projected from the result carried by this same dependent
runtime; no second body or semantic state can be supplied. -/
def Runtime.relaxedSuccess? {TapeIdentity : Type}
    (runtime : Runtime TapeIdentity) : Option (RelaxedSuccess runtime.body) :=
  match runtime.output.1 with
  | .error _ => none
  | .ok accepted => some accepted

theorem Runtime.relaxed_success_some_is_same_body
    {TapeIdentity : Type} (runtime : Runtime TapeIdentity)
    (accepted : RelaxedSuccess runtime.body)
    (success : runtime.relaxedSuccess? = some accepted) :
    runtime.output.1 = .ok accepted := by
  unfold Runtime.relaxedSuccess? at success
  cases result : runtime.output.1 with
  | error error => simp [result] at success
  | ok actual =>
      simp only [result, Option.some.injEq] at success
      simpa [success]

/-- Adversary and dynamically indexed verifier share one persistent native
oracle.  Parser and semantic failures, sampler exhaustion and suffix rejection
remain ordinary returned verifier results; scheduler failures remain native
terminal failures. -/
def rootCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls : Nat}
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls)
    (hidden : HiddenTape) :
    SchedulerNativeCursor globalOracleCalls (Runtime TapeIdentity) :=
  .machine configuration.adversaryLimits
    configuration.adversaryLimitBound .adversary emptyOracle
    (configuration.blackBox.start hidden configuration.observation)
    configuration.adversaryFuel empty_oracle_history_total_coherent
    (fun body proverFinalOracle proverCoherent =>
      .machine configuration.verifierLimits
        configuration.verifierLimitBound .verifier proverFinalOracle
        (compileScript
          (selectedVerifierScript configuration.binding body))
        verifierBudget proverCoherent
        (fun output verifierFinalOracle _ =>
          .returned
            { tapeIdentity := configuration.tapeIdentity hidden
              body := body
              proverFinalOracle := proverFinalOracle
              verifierFinalOracle := verifierFinalOracle
              output := output }))

def exposureCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls : Nat}
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls)
    (hidden : HiddenTape) : UnifiedExposureCursor globalOracleCalls :=
  (rootCursor configuration hidden).erase

def runDynamicRoot
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    SchedulerNativeRun (Runtime TapeIdentity) :=
  runSchedulerNative transitionFuel (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2

/-- The probability experiment observes the literal erasure of the very
result-carrying cursor that executed the dynamic semantic context. -/
theorem run_dynamic_root_trace_is_erased_exposure_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runDynamicRoot parameters configuration transitionFuel sample).trace =
      runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exposureCursor configuration sample.1) sample.2 := by
  exact run_scheduler_native_trace_eq_erased_unified_trace transitionFuel
    (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2

#print axioms successful_run_constructs_dynamic_context
#print axioms successful_run_has_canonical_wire
#print axioms Runtime.relaxed_success_some_is_same_body
#print axioms run_dynamic_root_trace_is_erased_exposure_trace

end
end AspisV8Completion.FSV8S7DynamicSelectedRoot

import ExtractionCollectorVerifiedSuccessfulReplay
import AspisFormal.K1.V7Tag73ExactCompilerResources

/-!
# A forward, same-body V8 root cursor

The older replay-facing leaves start after one challenge output has already
been programmed.  That state is too late to construct the causal ROM tree:
the corresponding query is cached and the paired transcript-advance answer is
not determined by a completed replay.

This file instead constructs the initial adversary and the selected V8
functional verifier as one scheduler cursor, before any master-tape answer is
read.  The verifier consumes exactly the body returned by that adversary
machine.  This is the source root needed by a future atomic restoration
client; it does not yet install that client or construct the 29-by-4 replay
matrix.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1400

namespace AspisV8Completion.FSV8ExactRootCursor

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ExactCompilerResources
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- Public/root inputs fixed before the unified random-oracle master tape.
There is no acceptance or extraction field. -/
structure Configuration
    (HiddenTape TapeIdentity Observation : Type)
    (globalOracleCalls n m : Nat) where
  blackBox : SameTapeBlackBox HiddenTape Observation Bytes
  tapeIdentity : HiddenTape → TapeIdentity
  observation : Observation
  adversaryLimits : OracleLimits
  verifierLimits : OracleLimits
  adversaryFuel : Nat
  firstWork : Point → Script Bytes Block Unit n
  secondWork : Point → Point → Script Bytes Block Unit m
  z : Fin 10 → K
  cuts : RootCuts
  initialDigest : Block
  adversaryLimitBound : adversaryLimits.totalCalls ≤ globalOracleCalls
  verifierLimitBound : verifierLimits.totalCalls ≤ globalOracleCalls

/-- Data returned only by the nested callbacks of `rootCursor`.  The dependent
type of `output` makes it impossible to pair a verifier record for one body
with a different adversary body. -/
structure Runtime (TapeIdentity : Type) (z : Fin 10 → K) where
  tapeIdentity : TapeIdentity
  body : Bytes
  proverFinalOracle : OracleState
  verifierFinalOracle : OracleState
  output : Except Error (Record body z) × Block

/-- The normal accepted projection is computed from the callback output.  It
does not accept a second body or record. -/
def Runtime.accepted? {TapeIdentity : Type} {z : Fin 10 → K}
    (runtime : Runtime TapeIdentity z) : Option (SelectedAccepted z) :=
  match runtime.output.1 with
  | .error _ => none
  | .ok record => some
      { body := runtime.body
        record := record
        finalDigest := runtime.output.2 }

theorem Runtime.accepted_some_has_same_body
    {TapeIdentity : Type} {z : Fin 10 → K}
    (runtime : Runtime TapeIdentity z) (accepted : SelectedAccepted z) :
    runtime.accepted? = some accepted → accepted.body = runtime.body := by
  intro exactAccepted
  cases runtime with
  | mk tapeIdentity body proverFinalOracle verifierFinalOracle output =>
      cases output with
      | mk result digest =>
          cases result with
          | error error => simp [Runtime.accepted?] at exactAccepted
          | ok record =>
              have same := Option.some.inj exactAccepted
              exact congrArg SelectedAccepted.body same.symm

/-- The exact forward V8 source cursor.  Abort, fuel exhaustion and oracle
resource failures remain the existing `SchedulerNativeTerminal.failed`
alternatives.  A normal verifier rejection is retained literally in
`Runtime.output`; it is not converted into success. -/
def rootCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) :
    SchedulerNativeCursor globalOracleCalls
      (Runtime TapeIdentity configuration.z) :=
  .machine configuration.adversaryLimits
    configuration.adversaryLimitBound .adversary emptyOracle
    (configuration.blackBox.start hidden configuration.observation)
    configuration.adversaryFuel empty_oracle_history_total_coherent
    (fun body proverFinalOracle proverCoherent =>
      .machine configuration.verifierLimits
        configuration.verifierLimitBound .verifier proverFinalOracle
        (compileScript (wholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts body
          configuration.initialDigest))
        (stagedBudget n m) proverCoherent
        (fun output verifierFinalOracle _ =>
          .returned
            { tapeIdentity := configuration.tapeIdentity hidden
              body := body
              proverFinalOracle := proverFinalOracle
              verifierFinalOracle := verifierFinalOracle
              output := output }))

/-- The result-free cursor used by the existing causal target tree is the
literal erasure of the result-carrying V8 cursor. -/
def exposureCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) : UnifiedExposureCursor globalOracleCalls :=
  (rootCursor configuration hidden).erase

/-- Execute that exact cursor on the one unified master tape used by the
causal target experiment. -/
def runExactRoot
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    SchedulerNativeRun (Runtime TapeIdentity configuration.z) :=
  runSchedulerNative transitionFuel (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2

/-- The causal tree observes the erasure of the very cursor producing the V8
root run, rather than an independently supplied exposure process. -/
theorem run_exact_root_trace_is_erased_exposure_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runExactRoot parameters configuration transitionFuel sample).trace =
      runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exposureCursor configuration sample.1) sample.2 := by
  exact run_scheduler_native_trace_eq_erased_unified_trace transitionFuel
    (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2

/-- The same hidden adversary start used by `rootCursor`, packaged through the
existing start-only collector origin.  This is an experiment-side producer;
the returned origin still exposes no hidden tape. -/
def sourceOrigin
    {HiddenTape TapeIdentity Observation Statement : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape)
    (finiteTape : FreshAnswerTape Block steps)
    (forgeryOf : Bytes → Option (PublicProof Statement Bytes)) :
    SameTapeExperimentOrigin TapeIdentity Observation Statement Bytes Bytes :=
  makeSameTapeExperimentOrigin configuration.blackBox hidden
    (configuration.tapeIdentity hidden) configuration.observation
    (controllerFromFreshAnswerTape finiteTape) configuration.adversaryLimits
    configuration.adversaryFuel emptyOracle forgeryOf

@[simp] theorem source_origin_first_execution
    {HiddenTape TapeIdentity Observation Statement : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape)
    (finiteTape : FreshAnswerTape Block steps)
    (forgeryOf : Bytes → Option (PublicProof Statement Bytes)) :
    (sourceOrigin configuration hidden finiteTape forgeryOf).firstExecution =
      runMachine (controllerFromFreshAnswerTape finiteTape)
        configuration.adversaryLimits .adversary configuration.adversaryFuel
        emptyOracle
        (configuration.blackBox.start hidden configuration.observation) := by
  rfl

@[simp] theorem source_origin_and_root_cursor_share_start
    {HiddenTape TapeIdentity Observation Statement : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape)
    (finiteTape : FreshAnswerTape Block steps)
    (forgeryOf : Bytes → Option (PublicProof Statement Bytes)) :
    (sourceOrigin configuration hidden finiteTape forgeryOf).capability.start
        configuration.observation =
      configuration.blackBox.start hidden configuration.observation := by
  rfl

@[simp] theorem root_cursor_uses_literal_hidden_start
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) :
    configuration.blackBox.start hidden configuration.observation =
      (closeSameTapeStart configuration.blackBox hidden
        (configuration.tapeIdentity hidden)).start configuration.observation := by
  rfl

/-- The exact-compiler target event specialized to the forward V8 cursor.
This imports the causal full-digest accounting without importing V7's
hard-wired future-free verifier. -/
def targetEvent
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) : Set (ExactCompilerSample HiddenTape parameters) :=
  exactCompilerTargetEvent parameters transitionFuel
    (exposureCursor configuration)

theorem target_probability_le_exact_count
    {HiddenTape TapeIdentity Observation : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (targetEvent parameters configuration transitionFuel) ≤
      exactCompilerExactCountError parameters := by
  exact exact_compiler_target_probability_le_exact_count hiddenLaw parameters
    transitionFuel (exposureCursor configuration)

theorem target_probability_le_raw_error
    {HiddenTape TapeIdentity Observation : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (targetEvent parameters configuration transitionFuel) ≤
      exactCompilerPositiveExposureError parameters := by
  exact exact_compiler_target_probability_le_div_two_pow_256 hiddenLaw
    parameters transitionFuel (exposureCursor configuration)

#print axioms root_cursor_uses_literal_hidden_start
#print axioms Runtime.accepted_some_has_same_body
#print axioms source_origin_first_execution
#print axioms source_origin_and_root_cursor_share_start
#print axioms run_exact_root_trace_is_erased_exposure_trace
#print axioms target_probability_le_exact_count
#print axioms target_probability_le_raw_error

end
end AspisV8Completion.FSV8ExactRootCursor

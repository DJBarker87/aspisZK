import FSV8S7DynamicSelectedRoot
import FSInterleavedSelectedIncrementBoundary
import SameBodySourceTerminalWeight

/-!
# Executed selected ordinary terminal

This leaf adds the arithmetic comparison which the S7 guard-relaxed root did
not execute.  Every operand is recomputed from the same submitted body and the
same staged transcript record:

* the canonical 697-field word and q22 records are parsed from `body`;
* the schedule, rho and alpha0 come from the selected middle run;
* alpha1--alpha3 come from the selected later run;
* the ordinary claim, chord and row scales come from the source-created
  functional description; and
* opened values and the positive query increment are recomputed by the same
  fail-closed pure opening preparation used by the selected suffix.

The expected side spells the selected Rust equation directly.  In particular,
the base covector is folded by alpha0--alpha3, the query covector only by
alpha1--alpha3, and the sparse image scalar is added at final slot three.

This is a functional selected-model endpoint.  Equality of the optimized Rust
structured contractions with these clear field expressions, and literal
Rust/Aeneas execution refinement, remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8S8SelectedOrdinaryTerminal

open scoped BigOperators
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge
open FSV8S7DynamicSelectedRoot
open FSAuthenticatedInterleavedPrefixMiddle
open FSInterleavedSelectedIncrementBoundary
open FSLiveSourceFunctionalMiddle
open SameBodyFunctionalProducerSource
open SameBodySourceRelationProducer
open SameBodyQueryClaim SameBodyQueryClaimExact SameBodyRelation
open AspisV8Completion.SameBodySourceTerminalWeight
open AspisV8.InterleavedChordRows
open AspisV8.TypedRelationTerminal
open AspisV8.PostQueryFunctional
open AspisV8.SelectedReceivedOracle
open AspisV8.SelectedPackedQueryBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge
open AspisPool.V7MerkleQueryExtractor
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ExactCompilerResources

abbrev Bytes := List UInt8
abbrev K := FSNonzeroQM31.K
abbrev B := FSBoundedTranscript.Block

noncomputable section

local instance : NeZero (2 : K) := AspisV8.SelectedReceivedOracle.twoNonzero

/-- Dense clear spelling of `Description::entry` before chord transport.
The inactive coefficient is the existing frozen selected mask-table function;
the three row terms use the actual semantic `z` and source-created scales. -/
def originalWeight (semantic : FSLiveSemanticPrefix.Success)
    (functional : Encoded) : Fin 1024 → K := fun index =>
  (List.finRange 3).foldl (fun out row =>
    let point := SameBodyPublicCorrection.points ordinaryOps semantic.z row
    let value := (List.finRange 10).foldl (fun product coordinate =>
      ordinaryOps.mul product
        (if index.val / 2^(9-coordinate.val) % 2 = 0
          then ordinaryOps.sub ordinaryOps.one (point coordinate)
          else point coordinate)) (functional.value.prepared.scales row)
    ordinaryOps.add out value) (inactiveCoefficient index)

/-- The selected source base covector after chord transport and alpha0 only.
The image term is deliberately not included here: the literal terminal adds it
separately at final slot three. -/
def ordinaryAfterAlpha0 {out : FSV7OODBodyScript.Result} {gamma : K} {body : Bytes}
    (semantic : FSLiveSemanticPrefix.Success)
    (middle : FSLiveSourceFunctionalMiddle.Success out gamma body semantic.z) :
    Fin 256 → K :=
  dualWeightFoldLayer 256 middle.middle.alpha0
    (transpose (middle.functional.value.prepared.abc 0)
      (middle.functional.value.prepared.abc 1)
      (middle.functional.value.prepared.abc 2)
      (originalWeight semantic middle.functional))

structure Operands where
  expected : K
  carried : K

/-- Recompute both sides of the selected ordinary terminal comparison.
Every failure (schedule shape, canonical parsing, record decoding or inverse
preparation) is retained as `none`; no default word, opening or weight exists.
-/
def operands {body : Bytes} (accepted : RelaxedSuccess body) : Option Operands := by
  classical
  let queries := accepted.record.middle.middle.queries
  if valid : FSQuerySchedule.ValidAccepted queries ∧ queries.length = 22 then
    let schedule := FSQuerySchedule.scheduleOf queries valid.1 valid.2
    match pureOpenedPreparation body schedule.positions
        accepted.record.middle.functional.data with
    | none => exact none
    | some prepared =>
      let word : Word K := fun i => prepared.wire.values.getD i.val 0
      let opened := recordFold accepted.record.middle.functional.data prepared.decoded
        schedule.positions prepared.inverses accepted.record.middle.middle.alpha0
      let ops := ringArithmetic (1 / 4 : K)
      let prior := ops.evaluate7
        (compact ops.toArithmetic accepted.record.middle.functional.value.claim
          (response word 0)) accepted.record.middle.middle.alpha0
      let afterQuery := ops.add prior
        (increment ops accepted.record.middle.middle.rho opened)
      let coins : Fin 3 → K :=
        ![accepted.record.suffix.alpha1, accepted.record.suffix.alpha2,
          accepted.record.suffix.alpha3]
      let final := finalValues word
      let foldedFinal := tailPrimal final (coins 0) (coins 1) (coins 2)
      let ordinaryTerminal := tailDual
        (ordinaryAfterAlpha0 accepted.semantic accepted.record.middle)
        (coins 0) (coins 1) (coins 2)
      let queryTerminal := tailDual
        (queryWeights
          (fun i => storedPoint (K := K) (schedule.positions i))
          accepted.record.middle.middle.rho)
        (coins 0) (coins 1) (coins 2)
      let image := imageTerminal accepted.record.middle.middle.tau
        (accepted.record.middle.functional.value.prepared.abc 1)
        (accepted.record.middle.functional.value.prepared.abc 2)
        accepted.record.middle.middle.alpha0 (coins 0) (coins 1) (coins 2)
      let expected := candidateClaim
        (fun i => ordinaryTerminal i + queryTerminal i) foldedFinal + image * foldedFinal 3
      let carried := terminalClaim ops word coins afterQuery
      exact some ⟨expected, carried⟩
  else exact none

def terminalAccepted? {body : Bytes} (accepted : RelaxedSuccess body) : Option Bool :=
  (operands accepted).map fun result => decide (result.expected = result.carried)

theorem terminalAccepted_true_iff {body : Bytes} (accepted : RelaxedSuccess body) :
    terminalAccepted? accepted = some true ↔
      ∃ result, operands accepted = some result ∧ result.expected = result.carried := by
  unfold terminalAccepted?
  cases resultEq : operands accepted with
  | none => simp
  | some result => simp

inductive Error where
  | source (error : FSV8S7DynamicSelectedRoot.Error)
  | terminalPreparation
  | relationTerminal

structure Success (body : Bytes) where
  relaxed : RelaxedSuccess body

/-- Same selected transcript program followed by the missing pure relation
comparison.  The comparison adds no oracle call and preserves the digest and
oracle returned by the source-shaped relaxed run. -/
def verifierScript (binding : FSLiveSemanticPrefix.Binding) (body : Bytes) :
    Script Bytes B (Except Error (Success body) × B) verifierBudget :=
  FSTranscriptScript.map (fun output =>
    match output.1 with
    | .error error => (.error (.source error), output.2)
    | .ok accepted =>
      match terminalAccepted? accepted with
      | none => (.error .terminalPreparation, output.2)
      | some false => (.error .relationTerminal, output.2)
      | some true => (.ok ⟨accepted⟩, output.2))
    (selectedVerifierScript binding body)

/-- Successful execution constructs both its original selected relaxed run and
the literal ordinary terminal equation.  Terminal acceptance is a consequence
of the executed Boolean, not an argument to this theorem. -/
theorem successful_run_constructs_terminal_equation
    (binding : FSLiveSemanticPrefix.Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle)
    (accepted : Success body) (digest : B)
    (success : (run tape (verifierScript binding body) oracle).1 =
      some (.ok accepted, digest)) :
    (run tape (selectedVerifierScript binding body) oracle).1 =
        some (.ok accepted.relaxed, digest) ∧
      ∃ result, operands accepted.relaxed = some result ∧
        result.expected = result.carried := by
  unfold verifierScript at success
  rw [run_map] at success
  cases sourceRun : (run tape (selectedVerifierScript binding body) oracle).1 with
  | none => simp [sourceRun] at success
  | some output =>
    rcases output with ⟨sourceResult, sourceDigest⟩
    cases sourceResult with
    | error error => simp [sourceRun] at success
    | ok relaxed =>
      cases terminalRun : terminalAccepted? relaxed with
      | none => simp [sourceRun, terminalRun] at success
      | some terminal =>
        cases terminal with
        | false => simp [sourceRun, terminalRun] at success
        | true =>
          simp [sourceRun, terminalRun] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨rfl, (terminalAccepted_true_iff relaxed).mp terminalRun⟩

/-- The terminal-checked run is observationally a post-processing of the same
selected transcript: its final oracle is exactly the relaxed run's final
oracle. -/
theorem verifierScript_final_oracle
    (binding : FSLiveSemanticPrefix.Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle) :
    (run tape (verifierScript binding body) oracle).2 =
      (run tape (selectedVerifierScript binding body) oracle).2 := by
  unfold verifierScript
  rw [run_map]

/-- Result of the native adversary/verifier scheduler after installing the
ordinary terminal comparison.  The body remains dependent: it is exactly the
bounded adversary's returned body. -/
structure Runtime (TapeIdentity : Type) where
  tapeIdentity : TapeIdentity
  body : Bytes
  proverFinalOracle : OracleState
  verifierFinalOracle : OracleState
  output : Except Error (Success body) × B

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
        (compileScript (verifierScript configuration.binding body))
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

def runRoot
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    SchedulerNativeRun (Runtime TapeIdentity) :=
  runSchedulerNative transitionFuel (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2

theorem run_root_trace_is_erased_exposure_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runRoot parameters configuration transitionFuel sample).trace =
      runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exposureCursor configuration sample.1) sample.2 := by
  exact run_scheduler_native_trace_eq_erased_unified_trace transitionFuel
    (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2

#print axioms terminalAccepted_true_iff
#print axioms successful_run_constructs_terminal_equation
#print axioms verifierScript_final_oracle
#print axioms run_root_trace_is_erased_exposure_trace

end
end AspisV8Completion.FSV8S8SelectedOrdinaryTerminal

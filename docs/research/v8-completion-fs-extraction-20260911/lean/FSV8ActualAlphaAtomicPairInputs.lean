import ExtractionCollectorOperationalSuccessfulReplay
import SuccessfulReplayAlphaBoundary
import FSV8AlphaChallengeInputBridge
import FSV8V7OracleMachineBridge

/-!
# Actual V8 alpha squeeze pair inputs

This leaf isolates the strongest atomic-pair fact currently constructible from
the V8 same-body execution and the start-only legal replay.

The source sampler does not make one abstract random-oracle request: its first
candidate begins with the two adjacent requests

* `digest ++ [1]` (candidate output), then
* `digest ++ [2]` (transcript advance).

The first request is also the literal driving input used by the successful
`constructLegalReplay` result.  Thus the two inputs required by an atomic
output/advance fork are constructed rather than supplied independently.

This is deliberately not a `PreparedConcreteRestoration`.  That V7 structure
also requires a `ConcreteRestorationNode` and an indexed
`FutureFreeTransition` taken from a `RawVerifierExecution`.  Neither object is
a field or consequence of `CoupledReplay`/`SuccessfulReplay`; producing that
cross-interpreter transition is the remaining interface obligation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8ActualAlphaAtomicPairInputs

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31
open FSV7OODSampler
open FSV8V7OracleMachineBridge
open FSV8AlphaChallengeInputBridge
open SuccessfulReplayAlphaBoundary
open ExtractionCollectorSuccessfulReplay

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- The two concrete byte strings consumed by the first source squeeze at the
actual alpha boundary. -/
def alphaAtomicPairInputs
    (afterAlphaNonce : FSBoundedTranscript.Transcript) : Bytes × Bytes :=
  (List.ofFn afterAlphaNonce.digest ++ [1],
    List.ofFn afterAlphaNonce.digest ++ [2])

@[simp] theorem alphaAtomicPairInputs_output
    (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    (alphaAtomicPairInputs afterAlphaNonce).1 =
      alphaCandidateInput afterAlphaNonce := by
  rfl

@[simp] theorem alphaAtomicPairInputs_advance
    (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    (alphaAtomicPairInputs afterAlphaNonce).2 =
      List.ofFn afterAlphaNonce.digest ++ [2] := by
  rfl

theorem alphaAtomicPairInputs_distinct
    (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    (alphaAtomicPairInputs afterAlphaNonce).1 ≠
      (alphaAtomicPairInputs afterAlphaNonce).2 := by
  simp [alphaAtomicPairInputs]

/-- The answer-dependent continuation after the first output/advance pair of
one candidate.  Naming it keeps the structural pair theorem small without
erasing the later limb and assembly behaviour. -/
def afterAlphaCandidateSqueeze (output advanced : Block) :
    OracleMachine (Except Error K × Block) :=
  compileScript
    (FSTranscriptScript.bind
      (pad (map (fun result => (result.1, result.2.1))
        (limbsScript 4 advanced (words output))) 0) fun
        (draw : Option (List Nat) × Block) =>
      match draw.1 with
      | none => .done (n := 0) (.error Error.limbExhausted, draw.2)
      | some limbs =>
          match assemble limbs with
          | none => .done (n := 0) (.error Error.assemblyFailure, draw.2)
          | some value => .done (n := 0) (.ok value, draw.2))

/-- Structural source fact: before any limb retry or zero retry can occur, the
compiled alpha candidate asks the output coordinate and then the matching
advance coordinate.  The continuation remains answer-dependent, as required
by the causal model. -/
theorem compiled_alpha_candidate_starts_with_atomic_pair
    (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    ∃ next : Block → Block →
        OracleMachine (Except Error K × Block),
      compileScript (candidateScript afterAlphaNonce.digest) =
        .query (alphaAtomicPairInputs afterAlphaNonce).1 (fun output =>
          .query (alphaAtomicPairInputs afterAlphaNonce).2
            (next output)) := by
  simp only [candidateScript, challengeScript, squeezeScript,
    FSTranscriptScript.bind,
    compileScript, alphaAtomicPairInputs]
  exact ⟨afterAlphaCandidateSqueeze, rfl⟩

/-- A successful legal replay at the actual same-body alpha boundary selects
the output half of the very same adjacent source pair.  No equality of field
values is used to infer equality of byte inputs. -/
theorem legal_replay_driving_input_is_actual_pair_output
    {TapeIdentity Observation Statement Proof : Type*}
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Bytes)
    (successful : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (afterAlphaNonce : FSBoundedTranscript.Transcript)
    (actual : IsActualAlphaBoundary successful afterAlphaNonce)
    (firstRunUse : ResourceUse) (forkOutput : ShaOutput)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (replay :
      {run : CoupledReplay TapeIdentity Statement Proof Bytes //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
              postForkController oracleLimits budget replayFuel)) run})
    (replayed :
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
              postForkController oracleLimits budget replayFuel)) =
        .ok replay) :
    IsActualAlphaBoundary successful afterAlphaNonce ∧
      replay.val.driving.input = (alphaAtomicPairInputs afterAlphaNonce).1 ∧
      (∃ entry,
        lookupEntry replay.val.replayRun.oracle
            (alphaAtomicPairInputs afterAlphaNonce).1 = some entry ∧
        entry.output = forkOutput) ∧
      ∃ next : Block → Block → OracleMachine (Except Error K × Block),
        compileScript (candidateScript afterAlphaNonce.digest) =
          .query (alphaAtomicPairInputs afterAlphaNonce).1 (fun output =>
            .query (alphaAtomicPairInputs afterAlphaNonce).2
              (next output)) := by
  have driving : replay.val.driving.input =
      (fixedFirstRunRecordFromOrigin origin
        (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
          postForkController oracleLimits budget replayFuel)).transcriptDrivingInput :=
    replay.property.2.2.2.2.1
  obtain ⟨entry, installed, outputEq⟩ :=
    constructLegalReplay_programmed_lookup origin.capability
      (fixedFirstRunRecordFromOrigin origin
        (alphaBoundaryConfiguration afterAlphaNonce firstRunUse forkOutput
          postForkController oracleLimits budget replayFuel)) replay replayed
  refine ⟨actual, ?_, ?_,
    compiled_alpha_candidate_starts_with_atomic_pair afterAlphaNonce⟩
  · simpa [alphaAtomicPairInputs, alphaBoundaryConfiguration,
      alphaCandidateInput] using driving
  · refine ⟨entry, ?_, ?_⟩
    · simpa [alphaAtomicPairInputs, alphaBoundaryConfiguration,
        alphaCandidateInput] using installed
    · simpa [alphaBoundaryConfiguration] using outputEq

#print axioms alphaAtomicPairInputs_output
#print axioms alphaAtomicPairInputs_advance
#print axioms alphaAtomicPairInputs_distinct
#print axioms afterAlphaCandidateSqueeze
#print axioms compiled_alpha_candidate_starts_with_atomic_pair
#print axioms legal_replay_driving_input_is_actual_pair_output

end
end AspisV8Completion.FSV8ActualAlphaAtomicPairInputs

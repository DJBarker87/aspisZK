import FSV8AlignedAlphaSqueezeStep
import FSV8FreshQueryRecord

/-!
# Initial-state disposition of one aligned alpha squeeze pair

The complete-duplex probability split is made at the state before either
half of a squeeze pair is queried.  `AlignedSqueezePair` already records the
literal origin of both calls, but its advance lookup is (correctly) stated at
the post-output state.  This leaf transports that lookup back to the initial
state using the distinct output/advance inputs.

No probability or independence claim is made.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1400

namespace AspisV8Completion.FSV8AlignedAlphaInitialPairDisposition

open FSBoundedTranscript
open FSV8AlignedAlphaSqueezeStep
open FSV8CandidateOriginTrace
open FSV8FreshQueryRecord
open FSV8V7OracleMachineBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- Exact source-facing split for the two calls of one squeeze pair, expressed
entirely at the state before the output call. -/
inductive InitialPairDisposition {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (v7 : OracleState) (s : Transcript)
    (pair : AlignedSqueezePair tape finiteTape limits v7 s) : Prop where
  | bothFresh
      (outputOrigin : pair.outputOrigin = .fresh)
      (advanceOrigin : pair.advanceOrigin = .fresh)
      (outputMissing : lookupEntry v7 (outputInput s) = none)
      (advanceMissing : lookupEntry v7 (advanceInput s) = none)
  | outputFreshAdvanceCached
      (outputOrigin : pair.outputOrigin = .fresh)
      (advanceOrigin : pair.advanceOrigin = .cached)
      (outputMissing : lookupEntry v7 (outputInput s) = none)
      (entry : TableEntry)
      (advanceFound : lookupEntry v7 (advanceInput s) = some entry)
  | outputCached
      (outputOrigin : pair.outputOrigin = .cached)
      (entry : TableEntry)
      (outputFound : lookupEntry v7 (outputInput s) = some entry)

private theorem lookup_freshQueryState_other
    (actor : QueryActor) (state : OracleState)
    (insertedInput otherInput : ShaInput) (output : ShaOutput)
    (different : insertedInput ≠ otherInput) :
    lookupEntry (freshQueryState actor state insertedInput output) otherInput =
      lookupEntry state otherInput := by
  unfold lookupEntry freshQueryState
  rw [List.find?_append]
  simp [different]

/-- The actual aligned pair constructs the initial-state three-way split.
The cached-output case deliberately leaves the advance half unrestricted:
once the returned output itself was already exposed, it belongs to the cached
branch of the later probability accounting. -/
theorem AlignedSqueezePair.initialDisposition
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s) :
    InitialPairDisposition tape finiteTape limits v7 s pair := by
  rcases pair.outputClassified with outputFresh | outputCached
  · rcases outputFresh with ⟨outputOrigin, outputMissing⟩
    have afterOutputExact :
        pair.afterOutput = freshQueryState .verifier v7 (outputInput s)
          (outputStep tape s).1 :=
      successful_missing_query_is_fresh_successor
        (controllerFromFreshAnswerTape finiteTape) limits .verifier v7
        pair.afterOutput (outputInput s) (outputStep tape s).1 outputMissing
        pair.outputRun
    have different : outputInput s ≠ advanceInput s := by
      simpa [outputInput, advanceInput] using
        squeeze_output_and_advance_inputs_are_distinct s.digest
    have advanceLookupExact :
        lookupEntry pair.afterOutput (advanceInput s) =
          lookupEntry v7 (advanceInput s) := by
      rw [afterOutputExact]
      exact lookup_freshQueryState_other .verifier v7 (outputInput s)
        (advanceInput s) (outputStep tape s).1 different
    rcases pair.advanceClassified with advanceFresh | advanceCached
    · rcases advanceFresh with ⟨advanceOrigin, advanceMissingAfter⟩
      exact .bothFresh outputOrigin advanceOrigin outputMissing
        (by simpa [advanceLookupExact] using advanceMissingAfter)
    · rcases advanceCached with ⟨advanceOrigin, entry, advanceFoundAfter⟩
      exact .outputFreshAdvanceCached outputOrigin advanceOrigin outputMissing
        entry (by simpa [advanceLookupExact] using advanceFoundAfter)
  · rcases outputCached with ⟨outputOrigin, entry, outputFound⟩
    exact .outputCached outputOrigin entry outputFound

#print axioms AlignedSqueezePair.initialDisposition

end
end AspisV8Completion.FSV8AlignedAlphaInitialPairDisposition

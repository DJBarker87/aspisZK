import FSV8AlignedAlphaCandidateSuffixSync
import FSV8ProgrammedAlphaCandidateWholeHistoryPrefix
import FSV8ReturnedBindKnownPrefix

/-!
# The accepted alpha final pair in the same verifier fresh enumeration

This source-shaped composition derives both chronological inclusions from the
actual machine runs and the same programmed cut.  The only alpha-side inputs
are the already constructed `SuccessfulAlignedChallenge` and its alignment
with the literal candidate machine terminal.  No pair interval or oracle-state
equality is accepted from the caller.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000

namespace AspisV8Completion.FSV8ProgrammedAlphaFinalPairFreshEnumeration

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73VerifierOracleStability
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutablePreAlphaFactorization FSV8ExecutableWholeFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ProgrammedAlphaCandidateWholeHistoryPrefix
open FSV8ReturnedBindKnownPrefix
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaCandidateSuffixSync FSV8CandidateOriginTrace

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- For the exact candidate run occurring inside one factored whole verifier,
a fresh accepted advance is a member of that whole verifier's literal fresh
query enumeration.  Candidate-to-whole nesting is constructed from the cut's
compiled bind, not supplied as a free interval premise. -/
theorem programmed_cut_final_pair_fresh_advance_mem_whole_enumeration
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (record : Record body z) (finalDigest : Block)
    (rootAligned : StateAligned tape finiteTape v7 fs)
    (wholeSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits .verifier
        fuel v7 (compileScript (factoredWholeStagedScript firstWork secondWork
          z cuts body digest))).halt = .returned (.ok record, finalDigest))
    (out : OODResult) (gamma : K) (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : FSV8BeforeAlphaMarkerFactorization.BeforeAlphaMarker
      out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      .verifier firstWork secondWork z body digest v7 fs fuel out gamma
      sourceDigest boundary preDigest before middle middleResultDigest)
    {start : Transcript} {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (startAligned : StateAligned tape finiteTape
      (preAlphaMachineRun finiteTape limits .verifier firstWork secondWork body
        digest v7 fuel out gamma z sourceDigest).oracle start.oracle)
    (success : SuccessfulAlignedChallenge tape finiteTape limits
      (preAlphaMachineRun finiteTape limits .verifier firstWork secondWork body
        digest v7 fuel out gamma z sourceDigest).oracle start blocks final value)
    (candidateAligned : StateAligned tape finiteTape
      (alphaCandidateMachineRun finiteTape limits .verifier firstWork
        secondWork body digest v7 fuel out gamma z sourceDigest boundary).oracle
      final.oracle) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits
        (preAlphaMachineRun finiteTape limits .verifier firstWork secondWork body
          digest v7 fuel out gamma z sourceDigest).oracle start rejected
        beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits beforeFinal
        finalStart,
        finalPair.advanceOrigin = .fresh →
          (advanceInput finalStart, (advanceStep tape finalStart).1) ∈
            freshQueryEnumeration (historySince v7
              (runMachine (controllerFromFreshAnswerTape finiteTape) limits
                .verifier fuel v7
                (compileScript (factoredWholeStagedScript firstWork secondWork
                  z cuts body digest))).oracle) := by
  let sourceRun := sourceMachineRun finiteTape limits .verifier firstWork
    secondWork body digest v7 fuel
  let preRun := preAlphaMachineRun finiteTape limits .verifier firstWork
    secondWork body digest v7 fuel out gamma z sourceDigest
  let candidateRun := alphaCandidateMachineRun finiteTape limits .verifier
    firstWork secondWork body digest v7 fuel out gamma z sourceDigest boundary
  let wholeRun := runMachine (controllerFromFreshAnswerTape finiteTape) limits
    .verifier fuel v7 (compileScript (factoredWholeStagedScript firstWork
      secondWork z cuts body digest))
  have rootToSource := runMachine_entry_history_prefix_final
    (controllerFromFreshAnswerTape finiteTape) limits .verifier fuel v7
    (compileScript (sourceThenGammaScript firstWork secondWork body digest))
  have sourceToPre := runMachine_entry_history_prefix_final
    (controllerFromFreshAnswerTape finiteTape) limits .verifier
    (fuel - sourceRun.steps) sourceRun.oracle
    (compileScript (preAlphaScript out gamma body z sourceDigest))
  have rootToSource' : v7.history <+: sourceRun.oracle.history := by
    simpa [sourceRun, sourceMachineRun] using rootToSource
  have rootToPre : v7.history <+: preRun.oracle.history := by
    exact rootToSource'.trans (by
      simpa [sourceRun, preRun, preAlphaMachineRun] using sourceToPre)
  obtain ⟨alpha0, candidateDigest, _candidateReturned, candidateToWhole⟩ :=
    programmed_cut_constructs_candidate_history_prefix_factored_whole
      finiteTape limits .verifier firstWork secondWork z cuts body digest v7 fs
      fuel record finalDigest rootAligned wholeSuccess out gamma sourceDigest
      boundary preDigest before middle middleResultDigest cutWitness
  obtain ⟨rejected, finalStart, beforeFinal, path, finalPair, routed⟩ :=
    successful_final_pair_fresh_advance_in_candidate_suffix
      (controllerFromFreshAnswerTape finiteTape)
      (((fuel - sourceRun.steps) - preRun.steps))
      (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
      (by simpa [preRun] using startAligned)
      (by simpa [candidateRun, alphaCandidateMachineRun, sourceRun,
        preRun] using candidateAligned) success
  refine ⟨rejected, finalStart, beforeFinal, path, finalPair, ?_⟩
  intro fresh
  obtain ⟨appended, freshRecord, candidateHistory, freshMember, inputExact,
      outputExact, originExact, _actorExact⟩ := routed fresh
  have inWhole := candidate_suffix_fresh_record_mem_enclosing_enumeration
    v7 preRun.oracle candidateRun.oracle wholeRun.oracle appended freshRecord
    rootToPre (by simpa [candidateRun, alphaCandidateMachineRun, sourceRun,
      preRun] using candidateHistory)
    (by simpa [candidateRun, wholeRun] using candidateToWhole)
    freshMember originExact
  simpa [inputExact, outputExact, wholeRun] using inWhole

#print axioms programmed_cut_final_pair_fresh_advance_mem_whole_enumeration

end
end AspisV8Completion.FSV8ProgrammedAlphaFinalPairFreshEnumeration

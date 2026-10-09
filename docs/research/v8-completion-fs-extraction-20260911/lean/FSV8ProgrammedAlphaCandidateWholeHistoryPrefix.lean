import FSV8ProgrammedAlphaCandidateHistoryPrefix

/-!
# The alpha candidate terminal is inside the same whole verifier

This composes the two source-derived bind factorizations.  Both prefixes use
the same `ProgrammedAlphaCutWitness` and the same successful factored whole
run; no interval or state-equality premise is accepted from the caller.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8ProgrammedAlphaCandidateWholeHistoryPrefix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutablePreAlphaFactorization FSV8ExecutableWholeFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ProgrammedPostAlphaHistoryPrefix
open FSV8ProgrammedAlphaCandidateHistoryPrefix

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

theorem programmed_cut_constructs_candidate_history_prefix_factored_whole
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (record : Record body z) (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (wholeSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredWholeStagedScript firstWork secondWork z cuts
          body digest))).halt = .returned (.ok record, finalDigest))
    (out : OODResult) (gamma : K) (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : FSV8BeforeAlphaMarkerFactorization.BeforeAlphaMarker
      out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      actor firstWork secondWork z body digest v7 fs fuel out gamma sourceDigest
      boundary preDigest before middle middleResultDigest) :
    let candidateRun := alphaCandidateMachineRun finiteTape limits actor
      firstWork secondWork body digest v7 fuel out gamma z sourceDigest boundary
    ∃ alpha0 candidateDigest,
      candidateRun.halt = .returned (.ok alpha0, candidateDigest) ∧
      candidateRun.oracle.history <+:
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
          v7 (compileScript (factoredWholeStagedScript firstWork secondWork z
            cuts body digest))).oracle.history := by
  obtain ⟨alpha0, candidateDigest, candidateReturned, candidateToPost⟩ :=
    programmed_cut_constructs_candidate_history_prefix finiteTape limits actor
      firstWork secondWork z body digest v7 fs fuel out gamma sourceDigest
      boundary preDigest before middle middleResultDigest cutWitness
  have postToWhole := programmed_postAlpha_history_prefix_factored_whole
    finiteTape limits actor firstWork secondWork z cuts body digest v7 fs fuel
    record finalDigest aligned wholeSuccess out gamma sourceDigest boundary
    preDigest before middle middleResultDigest cutWitness
  exact ⟨alpha0, candidateDigest, candidateReturned,
    candidateToPost.trans postToWhole⟩

#print axioms programmed_cut_constructs_candidate_history_prefix_factored_whole

end
end AspisV8Completion.FSV8ProgrammedAlphaCandidateWholeHistoryPrefix

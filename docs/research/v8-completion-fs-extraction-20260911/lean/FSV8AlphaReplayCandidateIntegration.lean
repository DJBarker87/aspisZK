import FSV8AlphaProgrammedCandidate
import FSV8AlphaChallengeInputBridge
import AspisFormal.K1.V7FsStateRestorationCoupling

/-!
# Legal alpha replay programming reaches the literal sampler

This leaf composes the generic start-only replay constructor's installed-table
invariant with the selected transcript decoder.  It does not prove that a
canonical alpha configuration is collected, nor does it assign probability to
the prior-target or absent branches.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSV8AlphaReplayCandidateIntegration

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open FSBoundedTranscript FSNonzeroQM31
open FSV8AlphaChallengeInputBridge
open FSV8V7OracleMachineBridge
open AlphaDigestEncodingProbe
open FSV8AlphaProgrammedCandidate

noncomputable section

def replayAlphaBoundary
    {TapeIdentity Statement Proof Result : Type*}
    (afterAlphaNonce : Transcript)
    (replay : CoupledReplay TapeIdentity Statement Proof Result) : Transcript :=
  { digest := afterAlphaNonce.digest
    oracle := projectOracleState replay.replayRun.oracle }

theorem legal_replay_programming_drives_alpha_candidate
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (afterAlphaNonce : Transcript)
    (firstRunUse : ResourceUse) (value : FSNonzeroQM31.K)
    (postForkController : AdaptiveController) (oracleLimits : OracleLimits)
    (budget : ResourceBudget) (replayFuel : Nat)
    (replay :
      {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse
              (canonicalOutput value) postForkController oracleLimits budget
              replayFuel)) run})
    (success :
      constructLegalReplay origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (alphaBoundaryConfiguration afterAlphaNonce firstRunUse
              (canonicalOutput value) postForkController oracleLimits budget
              replayFuel)) = .ok replay)
    (tape : FSBoundedTranscript.Tape) :
    (candidate tape (replayAlphaBoundary afterAlphaNonce replay.val)).1 =
      .ok value := by
  obtain ⟨entry, installed, outputEq⟩ :=
    constructLegalReplay_programmed_lookup origin.capability
      (fixedFirstRunRecordFromOrigin origin
        (alphaBoundaryConfiguration afterAlphaNonce firstRunUse
          (canonicalOutput value) postForkController oracleLimits budget
          replayFuel)) replay success
  have alphaLookup :
      lookupEntry replay.val.replayRun.oracle
        (alphaCandidateInput (replayAlphaBoundary afterAlphaNonce replay.val)) =
          some entry := by
    simpa [replayAlphaBoundary, alphaCandidateInput,
      alphaBoundaryConfiguration] using installed
  exact projected_lookup_drives_candidate tape replay.val.replayRun.oracle
    (replayAlphaBoundary afterAlphaNonce replay.val) entry value rfl alphaLookup
    outputEq

#print axioms legal_replay_programming_drives_alpha_candidate

end
end AspisV8Completion.FSV8AlphaReplayCandidateIntegration

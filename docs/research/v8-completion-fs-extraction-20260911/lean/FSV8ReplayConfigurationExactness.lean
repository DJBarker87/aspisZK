import FSV8AlphaChallengeInputBridge

/-!
# Exact boundary configuration reduction

The alpha and gamma replay-boundary constructors inherit every replay control
from the selected configuration and replace only its transcript-driving input.
This leaf proves that identifying a selected configuration with its actual
boundary configuration is therefore exactly the source-level byte-input
obligation.  It does not assume or construct that chronological equality.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000

namespace AspisV8Completion.FSV8ReplayConfigurationExactness

open AspisK1.V7FsStateRestorationCoupling
open FSV8GammaChallengeInputBridge
open FSV8AlphaChallengeInputBridge

noncomputable section

/-- With every replay control inherited from `configuration`, equality to the
actual gamma boundary is equivalent to equality of the one field replaced by
that constructor. -/
theorem configuration_eq_gammaBoundaryConfiguration_iff
    (configuration : OriginReplayConfiguration)
    (afterNonce : FSBoundedTranscript.Transcript) :
    configuration =
        gammaBoundaryConfiguration afterNonce
          configuration.firstRunUse configuration.forkOutput
          configuration.postForkController configuration.oracleLimits
          configuration.budget configuration.replayFuel ↔
      configuration.transcriptDrivingInput = gammaCandidateInput afterNonce := by
  cases configuration
  constructor
  · intro h
    exact congrArg OriginReplayConfiguration.transcriptDrivingInput h
  · intro h
    cases h
    rfl

/-- The corresponding reduction at the alpha boundary.  A later producer may
discharge the right-hand side from chronological execution; it cannot replace
it with matrix membership or equality of decoded challenge values. -/
theorem configuration_eq_alphaBoundaryConfiguration_iff
    (configuration : OriginReplayConfiguration)
    (afterAlphaNonce : FSBoundedTranscript.Transcript) :
    configuration =
        alphaBoundaryConfiguration afterAlphaNonce
          configuration.firstRunUse configuration.forkOutput
          configuration.postForkController configuration.oracleLimits
          configuration.budget configuration.replayFuel ↔
      configuration.transcriptDrivingInput =
        alphaCandidateInput afterAlphaNonce := by
  cases configuration
  constructor
  · intro h
    exact congrArg OriginReplayConfiguration.transcriptDrivingInput h
  · intro h
    cases h
    rfl

#print axioms configuration_eq_gammaBoundaryConfiguration_iff
#print axioms configuration_eq_alphaBoundaryConfiguration_iff

end
end AspisV8Completion.FSV8ReplayConfigurationExactness

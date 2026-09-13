import FSLiveChallengeV7Decode
import AspisFormal.K1.V7Tag73IncrementalSamplerControl

/-!
# Exact live alpha0 decoder bridge

A successful ordinary four-limb `FSBoundedTranscript.challenge` is accepted by
the deployed V7 `decodeChallengeParameter` at alpha round zero on exactly the
chronological blocks consumed by that live challenge.  This is deterministic
representation correspondence; it makes no freshness or probability claim.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8AlphaChallengeDecoderBridge

open FSLiveChallengeTrace FSLiveChallengeV7Decode
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

abbrev Tape := FSBoundedTranscript.Tape

theorem challenge_decode_alpha_zero
    (tape : Tape) (start : FSBoundedTranscript.Transcript)
    (limbs : List Nat)
    (success : (challenge tape start).result = some limbs) :
    decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        (challenge tape start).blocks =
      some (encodeQm31Limbs limbs) := by
  have decoded := challenge_decodeOrdinaryPrefix tape start limbs success
  have cap := (challenge_blocks_bounds tape start).2
  simp only [decodeChallengeParameter, samplerMode]
  unfold decodeOrdinaryExact
  rw [if_pos cap, decoded]
  rfl

theorem challenge_decode_alpha_zero_prefix_minimal
    (tape : Tape) (start : FSBoundedTranscript.Transcript)
    (limbs : List Nat)
    (success : (challenge tape start).result = some limbs) :
    forall count, count < (challenge tape start).blocks.length ->
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
          ((challenge tape start).blocks.take count) = none := by
  exact decodeChallengeParameter_accepted_is_prefix_minimal
    exactSecureCircleParameterMap (.alpha 0) (challenge tape start).blocks
      (encodeQm31Limbs limbs)
      (challenge_decode_alpha_zero tape start limbs success)

#print axioms challenge_decode_alpha_zero
#print axioms challenge_decode_alpha_zero_prefix_minimal

end AspisV8Completion.FSV8AlphaChallengeDecoderBridge

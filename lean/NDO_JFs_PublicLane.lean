import NDO_JFs_PaymentDigests
import NDO_JFu_DigestCheck
import RPz7_S6NativeForestHelpersV1
import RPz7_S6NativeDigestAcceptedInverseV1
set_option autoImplicit false
namespace AspisR1.JFs_PublicLane
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_accounts

theorem encoded : atomic_statement.encode_digest_canonical JFt_Digest44.value=
    ok JFs_PaymentDigests.bytes44 :=
  AspisS6NativeDigestAcceptedInverse.accepted_inverse _ _ JFs_PaymentDigests.decode44

theorem source : pool_v1_pair_forest_output_lane_v1 JFt_Digest44.value=ok (.Ok 3#u8) := by
  unfold pool_v1_pair_forest_output_lane_v1
  rw [AspisS6NativeForestHelpers.canonical_eq,JFu_DigestCheck.source _ JFt_Digest44.canonical]
  simp only [bind_tc_ok,Bool.true_eq,↓reduceIte]
  unfold first_canonical_byte
  rw [encoded]
  rfl

#print axioms encoded
#print axioms source
end AspisR1.JFs_PublicLane

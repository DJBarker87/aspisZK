import Hiq_CanonicalCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_CarrierIdentity
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames
open OraclePortStoredExperimentC4

theorem input_same (pub1 proof1 pub2 proof2 : Slice U8)
    (proof : bytesOf proof2.val = bytesOf proof1.val)
    (pub : bytesOf pub2.val = bytesOf pub1.val) :
    Hiq_CanonicalCarrier.input pub2 proof2 = Hiq_CanonicalCarrier.input pub1 proof1 := by
  unfold Hiq_CanonicalCarrier.input Hiq_CanonicalCarrier.submission
  rw [proof,pub]

/-- This equality includes the source-indexed statement tag and EVERY logical
proof message, not merely the erased proof or physical stored bytes. -/
theorem canonical_same (pub1 proof1 pub2 proof2 : Slice U8)
    (proof : bytesOf proof2.val = bytesOf proof1.val)
    (pub : bytesOf pub2.val = bytesOf pub1.val) :
    OraclePortStoredAdmissionC4.canonInput (Hiq_CanonicalCarrier.input pub2 proof2) =
      OraclePortStoredAdmissionC4.canonInput (Hiq_CanonicalCarrier.input pub1 proof1) := by
  rw [input_same pub1 proof1 pub2 proof2 proof pub]

theorem enriched_same (pub1 proof1 pub2 proof2 : Slice U8)
    (proof : bytesOf proof2.val = bytesOf proof1.val)
    (pub : bytesOf pub2.val = bytesOf pub1.val)
    (words1 words2 : CanonicalCutEnrichedTranscript.Words) (words : words2 = words1) :
    enrich words2 (Hiq_CanonicalCarrier.input pub2 proof2) =
      enrich words1 (Hiq_CanonicalCarrier.input pub1 proof1) := by
  rw [input_same pub1 proof1 pub2 proof2 proof pub,words]

#print axioms input_same
#print axioms canonical_same
#print axioms enriched_same
end AspisR1.Hiq_CarrierIdentity
end

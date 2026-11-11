import ExtractedPublicPreparationBinding
import ExtractedPublicCheckedBridge432
import PublicRawCoreAgreement
import R1PublicSourceRawSuccess

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.ActualPublicFieldBounds

/-- A successful actual generated semantic-public transcript serializes the
same fixed preparation projection, whose actual U32 asset/digest/frontier
coordinates are all canonical in the checked raw-u32 model.
PIN2 W3c: the transcript premise names the PIN2 `public_transcript` emission. -/
theorem public_transcript_fields_canonical
    {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize)
    (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.toPIN2
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
      hash c1 = ok (.Ok out)) :
    AspisR1.PublicSourceRaw.Canonical
      (AspisR1TerminalDecoder.PublicBinding.projectRaw s) := by
  obtain ⟨bytes, hbytes, _⟩ :=
    AspisR1PublicPreparation.PreparationBinding.helper_supplies_serializer_success
      D s hash c1 out h
  let p : AspisR1PublicSerializer.RawBridge431.Public :=
    AspisR1TerminalDecoder.PublicBinding.toSerializer s
  let rawBytes : AspisR1.PublicRawCore.Bytes :=
    bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte
  have hreturns : AspisR1PublicSerializer.RawBridge431.ExtractedReturns p rawBytes := by
    exact ⟨bytes, hbytes, rfl⟩
  have hcore : AspisR1.PublicRawCore.serialize
      (AspisR1PublicSerializer.RawBridge431.project p) = some rawBytes :=
    AspisR1PublicSerializer.RawBridge431.extracted_refines_core p rawBytes hreturns
  have hsource : AspisR1.PublicSourceRaw.serialize
      (AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw p) = some rawBytes := by
    change AspisR1.PublicSourceRaw.serialize
      (AspisR1.PublicRawCoreAgreement.fromCore (AspisR1PublicSerializer.RawBridge431.project p)) =
      some rawBytes
    rw [AspisR1.PublicRawCoreAgreement.serialize_fromCore]
    exact hcore
  have hc := AspisR1.PublicSourceRawSuccess.serialize_success_canonical
    (AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw p) rawBytes hsource
  simpa [p, AspisR1TerminalDecoder.PublicBinding.projectRaw] using hc

#print axioms public_transcript_fields_canonical
end AspisR1PublicPreparation.ActualPublicFieldBounds

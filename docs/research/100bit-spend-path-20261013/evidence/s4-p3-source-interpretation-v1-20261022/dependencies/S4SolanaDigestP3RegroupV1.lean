import ExtractedDigest32Callers
import ExtractedSourceDigestOracle
import ExtractedSourceDigestAddresses
import ExtractedDigest32Transcript
import R4Transport2OpeningChain
open Aeneas Aeneas.Std Result

namespace S4SolanaDigestP3RegroupV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.CallerStep
open AspisR1PublicPreparation.TranscriptStep
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisV8R19.DuplexFrames
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.R4Transport2OpeningChain

/-- One explicit model of the selected SolanaDigest/hashv wrapper under P3:
    the implementation hashes the concatenation of the supplied slices.
    `sha256` is intentionally an uninterpreted functional SHA implementation;
    this theorem does not prove SHA security or the SBF syscall implementation. -/
def solanaDigestP3Model {H : Type} (copyInst : core.marker.Copy H)
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize) :
    aspis_core.Digest32 H := {
  coremarkerCopyInst := copyInst
  digest := fun _ parts => ok (sha256 (flatten parts))
}

theorem opening_flatten (state : Bytes32) (tag : U8) (length : U32)
    (payload : Slice U8) :
    flatten (openingAbsorbParts state tag length payload) =
      AspisV8R19.SourceDuplexStep.bytes (decodeState state) ++ [0, decodeByte tag] ++
        (core.num.U32.to_le_bytes length).val.map decodeByte ++ rawBytes payload := by
  simp [openingAbsorbParts, flatten, Array.to_slice, Array.make, rawBytes,
    state_bytes, List.map_append, List.flatMap_append]

theorem opening_flatten_eq_source_absorb (state : Bytes32) (tag : U8)
    (length : U32) (payload framed : Slice U8)
    (hframe : rawBytes framed =
      (core.num.U32.to_le_bytes length).val.map decodeByte ++ rawBytes payload) :
    flatten (openingAbsorbParts state tag length payload) =
      flatten (absorbParts state tag framed) := by
  rw [opening_flatten, flatten_absorb]
  simp only [hframe, List.append_assoc]

theorem p3_digest_regroup {H : Type} (copyInst : core.marker.Copy H)
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize)
    (hash : H) (state : Bytes32) (tag : U8) (length : U32)
    (payload framed : Slice U8)
    (hframe : rawBytes framed =
      (core.num.U32.to_le_bytes length).val.map decodeByte ++ rawBytes payload) :
    (solanaDigestP3Model copyInst sha256).digest hash
        (openingAbsorbParts state tag length payload) =
      (solanaDigestP3Model copyInst sha256).digest hash
        (absorbParts state tag framed) := by
  simp only [solanaDigestP3Model]
  rw [opening_flatten_eq_source_absorb state tag length payload framed hframe]

theorem r4_framed_bytes (length : U32) (payload : Slice U8)
    (hlen : UScalar.cast .U32 (Slice.len payload) = length) :
    R4Transport2OpeningChain.framed payload =
      (core.num.U32.to_le_bytes length).val.map decodeByte ++ rawBytes payload := by
  simp only [R4Transport2OpeningChain.framed, SourceDigestAddresses.length_bytes, hlen]

theorem p3_digest_regroup_r4 {H : Type} (copyInst : core.marker.Copy H)
    (sha256 : AspisV8R19.DuplexFrames.Bytes → Array U8 32#usize)
    (hash : H) (state : Bytes32) (tag : U8) (length : U32)
    (payload framedSlice : Slice U8)
    (hraw : rawBytes framedSlice = R4Transport2OpeningChain.framed payload)
    (hlen : UScalar.cast .U32 (Slice.len payload) = length) :
    (solanaDigestP3Model copyInst sha256).digest hash
        (openingAbsorbParts state tag length payload) =
      (solanaDigestP3Model copyInst sha256).digest hash
        (absorbParts state tag framedSlice) := by
  apply p3_digest_regroup
  rw [hraw, r4_framed_bytes length payload hlen]

#print axioms opening_flatten_eq_source_absorb
#print axioms p3_digest_regroup
#print axioms p3_digest_regroup_r4
end S4SolanaDigestP3RegroupV1

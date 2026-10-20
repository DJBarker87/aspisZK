import ExtractedDigest32Callers
import ExtractedSourceDigestAddresses
import R1OpeningReseedFrame

/-! Byte-level source adapters for suffix row laws. No commitment-tree shape
is inspected: all roots remain arbitrary 32-byte digests. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.SamplerSuffixSourceFrames
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

/-- The P3 opening constructor hashes exactly the literal row-26 reseed. -/
theorem reseed_frame (s : Bytes32) (variant : transport.Variant) :
    flatten (CallerStep.reseedParts s variant) =
      AspisR1.OpeningReseedFrame.frame (decodeByte (CallerStep.variantTag variant))
        (decodeState s) := by
  simp [CallerStep.reseedParts, CallerStep.openingDomain, flatten,
    Array.to_slice, Array.make, AspisR1.OpeningReseedFrame.frame,
    AspisR1.TrailingStateFrame.frame, AspisR1.OpeningReseedFrame.domain,
    state_bytes] <;> decide

/-- The actual source tag for the deployed S2 path. Other variants do not
satisfy this theorem's conclusion. -/
theorem s2_tag : decodeByte (CallerStep.variantTag .S2) = (2 : AspisV8R19.DuplexFrames.Byte) := by
  apply Fin.ext
  rfl

/-- Exact framing for any opening payload, including digest || fold bytes
at row 30. Length is the source's explicit u32 length, not an assumed codec. -/
theorem opening_absorb_frame (s : Bytes32) (tag : U8) (n : U32)
    (payload : Slice U8) :
    flatten (CallerStep.openingAbsorbParts s tag n payload) =
      bytes (decodeState s) ++ [0, decodeByte tag] ++
        AspisR1.PublicInitFrame.lengthBytes n.val ++ rawBytes payload := by
  simp [CallerStep.openingAbsorbParts, flatten, Array.to_slice, Array.make,
    state_bytes, length_bytes, rawBytes, List.append_assoc]

/-- Source initializer success plus an interpretation of its single digest
call yields the carried row-26 reseeded state. -/
theorem reseed_state {Hash : Type} (D : aspis_core.Digest32 Hash)
    (hash : Hash) (s : Bytes32) (variant : transport.Variant)
    (after : transcript.Transcript Hash) (H : Bytes → State)
    (hnew : transcript.Transcript.new D hash s variant = ok after)
    (hdigest : ∀ out, D.digest hash (CallerStep.reseedParts s variant) = ok out →
      decodeState out = H (flatten (CallerStep.reseedParts s variant))) :
    decodeState after.state = H (AspisR1.OpeningReseedFrame.frame
      (decodeByte (CallerStep.variantTag variant)) (decodeState s)) := by
  obtain ⟨out, hout, rfl⟩ := CallerStep.opening_new_success D hash s variant after hnew
  rw [← reseed_frame]
  exact hdigest out hout

#print axioms reseed_frame
#print axioms s2_tag
#print axioms opening_absorb_frame
#print axioms reseed_state
end AspisR1PublicPreparation.SamplerSuffixSourceFrames

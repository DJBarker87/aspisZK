import R1SemanticPublicByteBinding
import R1SemanticPublicWireSurjective
import R1PublicInitFrame

/-! Exact coverage of the canonical bounded public carrier by the section-9
byte model, and the public initialization length bound. Source refinement
and the other transcript/hash-input bounds remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicCodecComplete
open SemanticPublicWire

theorem existsUnique_bytes (pub : R0P.Public M31)
    (hc : PublicOptionShape.canonical pub) (hi : pub.nextPairIndex < 2^64) :
    ∃! bytes : List Byte, parsePublic bytes = some pub := by
  obtain ⟨wire, hw⟩ := SemanticPublicWireSurjective.exists_wire pub hc hi
  have hwc : PublicOptionShape.canonical (toPublic wire) := hw.symm ▸ hc
  have hp : parsePublic (encode wire) = some pub := by
    rw [SemanticPublicWireRoundTrip.parsePublic_encode wire hwc, hw]
  exact ⟨encode wire, hp, fun bytes hb =>
    SemanticPublicByteBinding.bytes_unique bytes (encode wire) pub hb hp⟩

theorem parse_exists_iff (pub : R0P.Public M31) :
    (∃ bytes : List Byte, parsePublic bytes = some pub) ↔
      PublicOptionShape.canonical pub ∧ pub.nextPairIndex < 2^64 := by
  constructor
  · rintro ⟨bytes, hb⟩
    exact ⟨parsePublic_canonical bytes pub hb,
      SemanticPublicByteBinding.parsed_index_bound bytes pub hb⟩
  · rintro ⟨hc, hi⟩
    exact (existsUnique_bytes pub hc hi).exists

theorem parsed_length_bound (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) : bytes.length ≤ 1455 := by
  rw [SemanticPublicByteBinding.parsed_length bytes pub h]
  split <;> omega

theorem parsed_length_u32 (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) : bytes.length < 2^32 := by
  have hb := parsed_length_bound bytes pub h
  omega

theorem parsed_init_fits (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) : 75 + bytes.length ≤ 1530 := by
  have hb := parsed_length_bound bytes pub h
  omega

theorem parsed_init_frame_length (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) (c1 : AspisV8R19.SourceDuplexStep.State) :
    (PublicInitFrame.frame bytes c1).length =
      if pub.variant = .privateTransfer then 1530 else 1502 := by
  rw [PublicInitFrame.frame_length, SemanticPublicByteBinding.parsed_length bytes pub h]
  split <;> rfl

#print axioms existsUnique_bytes
#print axioms parse_exists_iff
#print axioms parsed_length_bound
#print axioms parsed_length_u32
#print axioms parsed_init_fits
#print axioms parsed_init_frame_length
end AspisR1.SemanticPublicCodecComplete

import R1SemanticPublicByteBinding
import PublicCodecAgreement

/-! PIN2 teeth: the extended section-9 parser rejects the old layout, a
destination on a transfer, a missing destination on a withdrawal, a
`has_destination` byte other than 0/1, and trailing bytes. -/
set_option autoImplicit false
namespace AspisR1.PIN2PublicWireTeeth

open AspisR1.SemanticPublicWire

/-- The pre-PIN2 lengths (1455 transfer, 1427 withdrawal) no longer parse. -/
theorem old_layout_rejected (bytes : List Byte)
    (h : bytes.length = 1455 ∨ bytes.length = 1427) : parsePublic bytes = none := by
  cases hp : parsePublic bytes with
  | none => rfl
  | some pub =>
      have hl := SemanticPublicByteBinding.parsed_length bytes pub hp
      split at hl <;> omega

theorem transfer_with_destination_rejected (c : Common) (r : Digest) (b : Bytes32)
    (hd : c.destination = some b) : parsePublic (encode (.transfer c r)) = none := by
  simp [parsePublic, SemanticPublicWireRoundTrip.decode_encode, toPublic,
    PublicOptionShape.check, hd]

theorem withdrawal_without_destination_rejected (c : Common) (a : M31)
    (hd : c.destination = none) : parsePublic (encode (.withdrawal c a)) = none := by
  simp [parsePublic, SemanticPublicWireRoundTrip.decode_encode, toPublic,
    PublicOptionShape.check, hd]

theorem bad_destination_tag (tag : Byte) (rest : List Byte) (h0 : tag ≠ 0) (h1 : tag ≠ 1) :
    readDestination (tag :: rest) = none := by
  simp [readDestination, h0, h1]

/-- Trailing bytes after a complete encoding are rejected (via the
compositional codec agreement). -/
theorem trailing_rejected (pub : PublicByteCodec.WirePublic) (rest : List Byte)
    (hne : rest ≠ []) :
    parsePublic (PublicByteCodec.publicCodec.emit pub ++ rest) = none := by
  rw [← PublicCodecAgreement.decode_eq_parsePublic]
  exact PublicByteCodec.decode_trailing pub rest hne

#print axioms old_layout_rejected
#print axioms transfer_with_destination_rejected
#print axioms withdrawal_without_destination_rejected
#print axioms bad_destination_tag
#print axioms trailing_rejected
end AspisR1.PIN2PublicWireTeeth

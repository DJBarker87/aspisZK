import R1SemanticPublicWire

/-! Round trips for the mathematical section-9 wire model. These facts do not
establish a Rust/source or account-binding correspondence.
PIN2 (2026-11-10): includes the appended pool/domain/destination suffix. -/
set_option autoImplicit false

namespace AspisR1.SemanticPublicWireRoundTrip

open AspisR1.SemanticPublicWire

private theorem readDigest_append (d : SemanticPublicWire.Digest)
    (tail : List SemanticPublicWire.Byte) :
    AspisR1.PublicByteCursor.read 32 PublicFieldBlockCodec.decodeDigest
      (PublicFieldBlockCodec.encodeDigest d ++ tail) = some (d, tail) :=
  AspisR1.PublicByteCursor.read_encoded 32 PublicFieldBlockCodec.decodeDigest
    PublicFieldBlockCodec.encodeDigest d tail
    PublicFieldBlockCodec.encodeDigest_length
    PublicFieldBlockCodec.decodeDigest_encodeDigest

private theorem readField_append (x : SemanticPublicWire.M31)
    (tail : List SemanticPublicWire.Byte) :
    AspisR1.PublicByteCursor.read 4 ExactLeafFieldCodec.decodeM31
      (ExactLeafFieldCodec.encodeM31 x ++ tail) = some (x, tail) :=
  AspisR1.PublicByteCursor.read_encoded 4 ExactLeafFieldCodec.decodeM31
    ExactLeafFieldCodec.encodeM31 x tail ExactLeafFieldCodec.encodeM31_length
    ExactLeafFieldCodec.decodeM31_encodeM31

private theorem readIndex_append (i : PublicIndexCodec.Index)
    (tail : List SemanticPublicWire.Byte) :
    AspisR1.PublicByteCursor.read 8 PublicIndexListCodec.decode
      (PublicIndexListCodec.encode i ++ tail) = some (i, tail) :=
  AspisR1.PublicByteCursor.read_encoded 8 PublicIndexListCodec.decode
    PublicIndexListCodec.encode i tail PublicIndexListCodec.encode_length8
    PublicIndexListCodec.decode_encode

private theorem readFrontier_append (f : SemanticPublicWire.Frontier)
    (tail : List SemanticPublicWire.Byte) :
    AspisR1.PublicByteCursor.read 640 PublicFieldBlockCodec.decodeFrontier
      (PublicFieldBlockCodec.encodeFrontier f ++ tail) = some (f, tail) :=
  AspisR1.PublicByteCursor.read_encoded 640 PublicFieldBlockCodec.decodeFrontier
    PublicFieldBlockCodec.encodeFrontier f tail
    PublicFieldBlockCodec.encodeFrontier_length
    PublicFieldBlockCodec.decodeFrontier_encodeFrontier

private theorem readBytes32_append (b : SemanticPublicWire.Bytes32)
    (tail : List SemanticPublicWire.Byte) :
    AspisR1.PublicByteCursor.read 32 SemanticPublicWire.decodeBytes32
      (SemanticPublicWire.encodeBytes32 b ++ tail) = some (b, tail) :=
  AspisR1.PublicByteCursor.read_encoded 32 SemanticPublicWire.decodeBytes32
    SemanticPublicWire.encodeBytes32 b tail
    SemanticPublicWire.encodeBytes32_length
    SemanticPublicWire.decodeBytes32_encodeBytes32

private theorem readDestination_append (d : Option SemanticPublicWire.Bytes32)
    (tail : List SemanticPublicWire.Byte) :
    SemanticPublicWire.readDestination (SemanticPublicWire.encodeDestination d ++ tail) =
      some (d, tail) := by
  cases d with
  | none => simp [SemanticPublicWire.encodeDestination, SemanticPublicWire.readDestination]
  | some b =>
      simp [SemanticPublicWire.encodeDestination, SemanticPublicWire.readDestination,
        SemanticPublicWire.readBytes32, readBytes32_append]

private theorem decodeAfter_afterBytes (c : Common) :
    SemanticPublicWire.decodeAfter c.anchor c.nullifier c.assetId c.change
      (SemanticPublicWire.afterBytes c) = some c := by
  have hlast : SemanticPublicWire.readDestination
      (SemanticPublicWire.encodeDestination c.destination) = some (c.destination, []) := by
    simpa only [List.append_nil] using readDestination_append c.destination []
  simp [SemanticPublicWire.decodeAfter, SemanticPublicWire.afterBytes,
    SemanticPublicWire.bindingBytes,
    SemanticPublicWire.readIndex, SemanticPublicWire.readFrontier,
    SemanticPublicWire.readDigest, SemanticPublicWire.readBytes32,
    List.append_assoc, readIndex_append,
    readFrontier_append, readDigest_append, readBytes32_append, hlast]

private theorem decodeTransfer_encoded (c : Common) (recipient : Digest) :
    SemanticPublicWire.decodeTransfer
      (SemanticPublicWire.header c ++ [1] ++
        PublicFieldBlockCodec.encodeDigest recipient ++
        PublicFieldBlockCodec.encodeDigest c.change ++ [0] ++
        SemanticPublicWire.afterBytes c) = some (.transfer c recipient) := by
  simp [SemanticPublicWire.decodeTransfer, SemanticPublicWire.header,
    SemanticPublicWire.readDigest, SemanticPublicWire.readField,
    List.append_assoc, readDigest_append, readField_append,
    decodeAfter_afterBytes, SemanticPublicWire.expect]

private theorem decodeWithdrawal_encoded (c : Common) (amount : M31) :
    SemanticPublicWire.decodeWithdrawal
      (SemanticPublicWire.header c ++ [0] ++
        PublicFieldBlockCodec.encodeDigest c.change ++ [1] ++
        ExactLeafFieldCodec.encodeM31 amount ++ SemanticPublicWire.afterBytes c) =
      some (.withdrawal c amount) := by
  simp [SemanticPublicWire.decodeWithdrawal, SemanticPublicWire.header,
    SemanticPublicWire.readDigest, SemanticPublicWire.readField,
    List.append_assoc, readDigest_append, readField_append,
    decodeAfter_afterBytes, SemanticPublicWire.expect]

theorem decode_encode (wire : Wire) : SemanticPublicWire.decode (encode wire) = some wire := by
  cases wire with
  | transfer c recipient =>
      simpa only [SemanticPublicWire.encode, List.singleton_append, List.cons_append, List.nil_append,
        SemanticPublicWire.decode, if_pos, Fin.zero_ne_one, if_false] using
        decodeTransfer_encoded c recipient
  | withdrawal c amount =>
      simpa only [SemanticPublicWire.encode, List.singleton_append, List.cons_append, List.nil_append,
        SemanticPublicWire.decode, if_pos, show (1 : Byte) ≠ 0 by decide, if_false] using
        decodeWithdrawal_encoded c amount

private theorem header_length (c : Common) :
    (SemanticPublicWire.header c).length = 68 := by
  simp [SemanticPublicWire.header, PublicFieldBlockCodec.encodeDigest_length,
    ExactLeafFieldCodec.encodeM31_length]

theorem encodeDestination_length (d : Option SemanticPublicWire.Bytes32) :
    (SemanticPublicWire.encodeDestination d).length =
      match d with
      | none => 1
      | some _ => 33 := by
  cases d with
  | none => rfl
  | some b => simp [SemanticPublicWire.encodeDestination, SemanticPublicWire.encodeBytes32_length]

private theorem afterBytes_length (c : Common) :
    (SemanticPublicWire.afterBytes c).length =
      1384 + (SemanticPublicWire.encodeDestination c.destination).length := by
  simp [SemanticPublicWire.afterBytes, SemanticPublicWire.bindingBytes,
    PublicIndexListCodec.encode_length8,
    PublicFieldBlockCodec.encodeFrontier_length,
    PublicFieldBlockCodec.encodeDigest_length,
    SemanticPublicWire.encodeBytes32_length]
  omega

/-- PIN2: the old section-9 lengths (1455 transfer, 1427 withdrawal) plus the
64-byte pool/domain suffix and the destination field (1 or 33 bytes). -/
theorem encode_length (wire : Wire) :
    (encode wire).length =
      match wire with
      | .transfer c _ => 1519 + (SemanticPublicWire.encodeDestination c.destination).length
      | .withdrawal c _ => 1491 + (SemanticPublicWire.encodeDestination c.destination).length := by
  cases wire with
  | transfer c recipient =>
      simp [SemanticPublicWire.encode, header_length, afterBytes_length,
        PublicFieldBlockCodec.encodeDigest_length]
      omega
  | withdrawal c amount =>
      simp [SemanticPublicWire.encode, header_length, afterBytes_length,
        PublicFieldBlockCodec.encodeDigest_length,
        ExactLeafFieldCodec.encodeM31_length]
      omega

/-- PIN2: canonical lengths, 1520 bytes for a transfer and 1524 for a withdrawal. -/
theorem encode_length_canonical (wire : Wire)
    (hcanonical : PublicOptionShape.canonical (toPublic wire)) :
    (encode wire).length =
      match wire with
      | .transfer _ _ => 1520
      | .withdrawal _ _ => 1524 := by
  rw [encode_length]
  cases wire with
  | transfer c recipient =>
      have hd : (toPublic (.transfer c recipient)).destination = none :=
        PublicOptionShape.private_transfer_destination _ rfl hcanonical
      cases hc : c.destination with
      | none => simp [hc, encodeDestination_length]
      | some b => simp [toPublic, hc] at hd
  | withdrawal c amount =>
      obtain ⟨d, hd, _⟩ := PublicOptionShape.withdrawal_destination _ rfl hcanonical
      cases hc : c.destination with
      | none => simp [toPublic, hc] at hd
      | some b => simp [hc, encodeDestination_length]

theorem parsePublic_encode (wire : Wire)
    (hcanonical : PublicOptionShape.canonical (toPublic wire)) :
    SemanticPublicWire.parsePublic (encode wire) = some (toPublic wire) := by
  have hcheck : PublicOptionShape.check (toPublic wire) = true :=
    (PublicOptionShape.check_eq_true_iff (toPublic wire)).2 hcanonical
  simp [SemanticPublicWire.parsePublic, decode_encode, hcheck]

end AspisR1.SemanticPublicWireRoundTrip

#print axioms AspisR1.SemanticPublicWireRoundTrip.decode_encode
#print axioms AspisR1.SemanticPublicWireRoundTrip.encode_length
#print axioms AspisR1.SemanticPublicWireRoundTrip.encode_length_canonical
#print axioms AspisR1.SemanticPublicWireRoundTrip.parsePublic_encode

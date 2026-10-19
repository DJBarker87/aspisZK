import R1SemanticPublicWire

/-! Round trips for the mathematical section-9 wire model. These facts do not
establish a Rust/source or account-binding correspondence. -/
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

private theorem decodeAfter_afterBytes (c : Common) :
    SemanticPublicWire.decodeAfter c.anchor c.nullifier c.assetId c.change
      (SemanticPublicWire.afterBytes c) = some c := by
  have hlast : PublicByteCursor.read 640 PublicFieldBlockCodec.decodeFrontier
      (PublicFieldBlockCodec.encodeFrontier c.nextFrontier) = some (c.nextFrontier, []) := by
    simpa only [List.append_nil] using readFrontier_append c.nextFrontier []
  simp [SemanticPublicWire.decodeAfter, SemanticPublicWire.afterBytes,
    SemanticPublicWire.readIndex, SemanticPublicWire.readFrontier,
    SemanticPublicWire.readDigest,
    List.append_assoc, readIndex_append,
    readFrontier_append, readDigest_append, hlast]

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

private theorem afterBytes_length (c : Common) :
    (SemanticPublicWire.afterBytes c).length = 1320 := by
  simp [SemanticPublicWire.afterBytes, PublicIndexListCodec.encode_length8,
    PublicFieldBlockCodec.encodeFrontier_length,
    PublicFieldBlockCodec.encodeDigest_length]

theorem encode_length (wire : Wire) :
    (encode wire).length =
      match wire with
      | .transfer _ _ => 1455
      | .withdrawal _ _ => 1427 := by
  cases wire with
  | transfer c recipient =>
      simp [SemanticPublicWire.encode, header_length, afterBytes_length,
        PublicFieldBlockCodec.encodeDigest_length]
  | withdrawal c amount =>
      simp [SemanticPublicWire.encode, header_length, afterBytes_length,
        PublicFieldBlockCodec.encodeDigest_length,
        ExactLeafFieldCodec.encodeM31_length]

theorem parsePublic_encode (wire : Wire)
    (hcanonical : PublicOptionShape.canonical (toPublic wire)) :
    SemanticPublicWire.parsePublic (encode wire) = some (toPublic wire) := by
  have hcheck : PublicOptionShape.check (toPublic wire) = true :=
    (PublicOptionShape.check_eq_true_iff (toPublic wire)).2 hcanonical
  simp [SemanticPublicWire.parsePublic, decode_encode, hcheck]

end AspisR1.SemanticPublicWireRoundTrip

#print axioms AspisR1.SemanticPublicWireRoundTrip.decode_encode
#print axioms AspisR1.SemanticPublicWireRoundTrip.encode_length
#print axioms AspisR1.SemanticPublicWireRoundTrip.parsePublic_encode

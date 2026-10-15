import R1SemanticPublicWire

/-! Round trips for the mathematical section-9 wire model. These facts do not
establish a Rust/source or account-binding correspondence. -/
set_option autoImplicit false

namespace AspisR1.SemanticPublicWireRoundTrip

open AspisR1.SemanticPublicWire
open AspisR1.PublicFieldBlockCodec
open AspisR1.ExactLeafFieldCodec

private theorem readDigest_append (d : Digest) (tail : List Byte) :
    readDigest (encodeDigest d ++ tail) = some (d, tail) :=
  AspisR1.PublicByteCursor.read_encoded 32 decodeDigest encodeDigest d tail
    encodeDigest_length decodeDigest_encodeDigest

private theorem readField_append (x : M31) (tail : List Byte) :
    readField (encodeM31 x ++ tail) = some (x, tail) :=
  AspisR1.PublicByteCursor.read_encoded 4 decodeM31 encodeM31 x tail
    encodeM31_length decodeM31_encodeM31

private theorem readIndex_append (i : PublicIndexCodec.Index) (tail : List Byte) :
    readIndex (PublicIndexListCodec.encode i ++ tail) = some (i, tail) :=
  AspisR1.PublicByteCursor.read_encoded 8 PublicIndexListCodec.decode
    PublicIndexListCodec.encode i tail PublicIndexListCodec.encode_length8
    PublicIndexListCodec.decode_encode

private theorem readFrontier_append (f : Frontier) (tail : List Byte) :
    readFrontier (encodeFrontier f ++ tail) = some (f, tail) :=
  AspisR1.PublicByteCursor.read_encoded 640 decodeFrontier encodeFrontier f tail
    encodeFrontier_length decodeFrontier_encodeFrontier

private theorem decodeAfter_afterBytes (c : Common) :
    decodeAfter c.anchor c.nullifier c.assetId c.change (afterBytes c) = some c := by
  have hfinal := readFrontier_append c.nextFrontier []
  simp [decodeAfter, afterBytes, readIndex_append, readFrontier_append,
    readDigest_append, List.append_assoc, hfinal]

private theorem decodeTransfer_encoded (c : Common) (recipient : Digest) :
    decodeTransfer
      (header c ++ [1] ++ encodeDigest recipient ++ encodeDigest c.change ++
        [0] ++ afterBytes c) = some (.transfer c recipient) := by
  simp [decodeTransfer, header, List.append_assoc, readDigest_append,
    readField_append, decodeAfter_afterBytes, expect]

private theorem decodeWithdrawal_encoded (c : Common) (amount : M31) :
    decodeWithdrawal
      (header c ++ [0] ++ encodeDigest c.change ++ [1] ++ encodeM31 amount ++
        afterBytes c) = some (.withdrawal c amount) := by
  simp [decodeWithdrawal, header, List.append_assoc, readDigest_append,
    readField_append, decodeAfter_afterBytes, expect]

theorem decode_encode (wire : Wire) : decode (encode wire) = some wire := by
  cases wire with
  | transfer c recipient =>
      simp [encode, decode, decodeTransfer_encoded]
  | withdrawal c amount =>
      simp [encode, decode, decodeWithdrawal_encoded]

private theorem header_length (c : Common) : (header c).length = 68 := by
  simp [header, encodeDigest_length, ExactLeafFieldCodec.encodeM31_length]

private theorem afterBytes_length (c : Common) : (afterBytes c).length = 1320 := by
  simp [afterBytes, PublicIndexListCodec.encode_length8,
    encodeFrontier_length, encodeDigest_length]

theorem encode_length (wire : Wire) :
    (encode wire).length =
      match wire with
      | .transfer _ _ => 1455
      | .withdrawal _ _ => 1427 := by
  cases wire with
  | transfer c recipient =>
      simp [encode, header_length, afterBytes_length]
  | withdrawal c amount =>
      simp [encode, header_length, afterBytes_length]

theorem parsePublic_encode (wire : Wire)
    (hcanonical : PublicOptionShape.canonical (toPublic wire)) :
    parsePublic (encode wire) = some (toPublic wire) := by
  have hcheck : PublicOptionShape.check (toPublic wire) = true :=
    (PublicOptionShape.check_eq_true_iff (toPublic wire)).2 hcanonical
  simp [parsePublic, decode_encode, hcheck]

end AspisR1.SemanticPublicWireRoundTrip

#print axioms AspisR1.SemanticPublicWireRoundTrip.decode_encode
#print axioms AspisR1.SemanticPublicWireRoundTrip.encode_length
#print axioms AspisR1.SemanticPublicWireRoundTrip.parsePublic_encode

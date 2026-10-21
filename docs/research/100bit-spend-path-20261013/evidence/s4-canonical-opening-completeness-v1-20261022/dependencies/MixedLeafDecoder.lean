import R1FixedWidthDecoder
import R1MixedLeafSlices

/-! Strict constructive decoders for the current mixed leaf encodings.
These are byte-list model results, not a Rust source-refinement theorem. -/
set_option autoImplicit false

namespace AspisR1.MixedLeafDecoder

open AspisR1.ExactLeafFieldCodec AspisR1.MixedLeafEncoding

def decodeC1Slot (bytes : List Byte) : Option C1Slot := do
  let words ← AspisR1.FixedWidthDecoder.decode decodeM31 4 26 (bytes.take 104)
  let tail ← decodeQM31 (bytes.drop 104)
  pure (words, tail)

def decodeC2Slot (bytes : List Byte) : Option C2Slot :=
  AspisR1.FixedWidthDecoder.decode decodeQM31 16 2 bytes

def decodeC1 (bytes : List Byte) : Option C1 :=
  AspisR1.FixedWidthDecoder.decode decodeC1Slot 120 4 bytes

def decodeC2 (bytes : List Byte) : Option C2 :=
  AspisR1.FixedWidthDecoder.decode decodeC2Slot 32 4 bytes

theorem decodeC1Slot_encode (x : C1Slot) :
    decodeC1Slot (encodeC1Slot x) = some x := by
  have hw := AspisR1.FixedWidthDecoder.decode_encode decodeM31 encodeM31 4 26 x.1
    encodeM31_length decodeM31_encodeM31
  unfold decodeC1Slot
  rw [AspisR1.MixedLeafSlices.c1Slot_take_words,
    AspisR1.MixedLeafSlices.c1Slot_drop_words]
  change AspisR1.FixedWidthDecoder.decode decodeM31 4 26
    (AspisR1.FixedWidthDecoder.encode encodeM31 x.1) = some x.1 at hw
  change (AspisR1.FixedWidthDecoder.decode decodeM31 4 26
    (AspisR1.FixedWidthDecoder.encode encodeM31 x.1)).bind _ = _
  rw [hw]
  simp [decodeQM31_encodeQM31]

theorem encodeC1Slot_of_decode (bytes : List Byte) (x : C1Slot)
    (h : decodeC1Slot bytes = some x) : encodeC1Slot x = bytes := by
  cases hw : AspisR1.FixedWidthDecoder.decode decodeM31 4 26 (bytes.take 104) with
  | none => simp [decodeC1Slot, hw] at h
  | some words =>
      cases ht : decodeQM31 (bytes.drop 104) with
      | none => simp [decodeC1Slot, hw, ht] at h
      | some tail =>
          have hx : (words, tail) = x := by simpa [decodeC1Slot, hw, ht] using h
          rw [← hx]
          have hwenc := AspisR1.FixedWidthDecoder.encode_of_decode decodeM31 encodeM31
            4 26 (bytes.take 104) words hw encodeM31_of_decodeM31
          change AspisR1.FixedWidthDecoder.encode encodeM31 words ++ encodeQM31 tail = bytes
          rw [hwenc, encodeQM31_of_decodeQM31 _ _ ht]
          exact List.take_append_drop 104 bytes

theorem decodeC2Slot_encode (x : C2Slot) :
    decodeC2Slot (encodeC2Slot x) = some x := by
  exact AspisR1.FixedWidthDecoder.decode_encode decodeQM31 encodeQM31 16 2 x
    encodeQM31_length decodeQM31_encodeQM31

theorem encodeC2Slot_of_decode (bytes : List Byte) (x : C2Slot)
    (h : decodeC2Slot bytes = some x) : encodeC2Slot x = bytes := by
  exact AspisR1.FixedWidthDecoder.encode_of_decode decodeQM31 encodeQM31 16 2 bytes x h
    encodeQM31_of_decodeQM31

theorem decodeC1_encode (x : C1) : decodeC1 (encodeC1 x) = some x := by
  exact AspisR1.FixedWidthDecoder.decode_encode decodeC1Slot encodeC1Slot 120 4 x
    encodeC1Slot_length decodeC1Slot_encode

theorem encodeC1_of_decode (bytes : List Byte) (x : C1)
    (h : decodeC1 bytes = some x) : encodeC1 x = bytes := by
  exact AspisR1.FixedWidthDecoder.encode_of_decode decodeC1Slot encodeC1Slot 120 4 bytes x h
    encodeC1Slot_of_decode

theorem decodeC2_encode (x : C2) : decodeC2 (encodeC2 x) = some x := by
  exact AspisR1.FixedWidthDecoder.decode_encode decodeC2Slot encodeC2Slot 32 4 x
    encodeC2Slot_length decodeC2Slot_encode

theorem encodeC2_of_decode (bytes : List Byte) (x : C2)
    (h : decodeC2 bytes = some x) : encodeC2 x = bytes := by
  exact AspisR1.FixedWidthDecoder.encode_of_decode decodeC2Slot encodeC2Slot 32 4 bytes x h
    encodeC2Slot_of_decode

theorem decodeC1_eq_some_iff (bytes : List Byte) (x : C1) :
    decodeC1 bytes = some x ↔ encodeC1 x = bytes := by
  constructor
  · exact encodeC1_of_decode bytes x
  · intro h
    rw [← h]
    exact decodeC1_encode x

theorem decodeC2_eq_some_iff (bytes : List Byte) (x : C2) :
    decodeC2 bytes = some x ↔ encodeC2 x = bytes := by
  constructor
  · exact encodeC2_of_decode bytes x
  · intro h
    rw [← h]
    exact decodeC2_encode x

theorem decodeC1_length (bytes : List Byte) (x : C1)
    (h : decodeC1 bytes = some x) : bytes.length = 480 := by
  rw [← encodeC1_of_decode bytes x h]
  exact encodeC1_length x

theorem decodeC2_length (bytes : List Byte) (x : C2)
    (h : decodeC2 bytes = some x) : bytes.length = 128 := by
  rw [← encodeC2_of_decode bytes x h]
  exact encodeC2_length x

#print axioms decodeC1Slot_encode
#print axioms encodeC1Slot_of_decode
#print axioms decodeC2Slot_encode
#print axioms encodeC2Slot_of_decode
#print axioms decodeC1_encode
#print axioms encodeC1_of_decode
#print axioms decodeC2_encode
#print axioms encodeC2_of_decode
#print axioms decodeC1_eq_some_iff
#print axioms decodeC2_eq_some_iff
#print axioms decodeC1_length
#print axioms decodeC2_length

end AspisR1.MixedLeafDecoder

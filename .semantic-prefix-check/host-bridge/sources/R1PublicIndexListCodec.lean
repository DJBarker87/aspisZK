import R1PublicIndexCodec
import R1ListFieldCodec

/-! A list-level wrapper for the mathematical eight-byte public-index codec.
This records exact width and successful round trips, without claiming a Rust
parser or caller correspondence. -/
set_option autoImplicit false

namespace AspisR1.PublicIndexListCodec

open AspisR1.RetainedFieldByteCodec

abbrev Byte := RetainedFieldByteCodec.Byte
abbrev Index := PublicIndexCodec.Index

def encode (x : Index) : List Byte :=
  List.ofFn (PublicIndexCodec.encode x)

def decode (bytes : List Byte) : Option Index :=
  (RetainedFieldByteCodec.fixedBytes? 8 bytes).map PublicIndexCodec.decode

theorem encode_length8 (x : Index) : (encode x).length = 8 := by
  simp [encode]

theorem decode_encode (x : Index) : decode (encode x) = some x := by
  change (RetainedFieldByteCodec.fixedBytes? 8
    (List.ofFn (PublicIndexCodec.encode x))).map PublicIndexCodec.decode = some x
  rw [ListFieldCodec.fixedBytes?_ofFn]
  exact congrArg some (PublicIndexCodec.decode_encode x)

theorem encode_of_decode (bytes : List Byte) (x : Index)
    (h : decode bytes = some x) : encode x = bytes := by
  cases hfixed : RetainedFieldByteCodec.fixedBytes? 8 bytes with
  | none => simp [decode, hfixed] at h
  | some wordBytes =>
      have hdecode : PublicIndexCodec.decode wordBytes = x := by
        simpa [decode, hfixed] using h
      calc
        encode x = List.ofFn
            (PublicIndexCodec.encode (PublicIndexCodec.decode wordBytes)) := by
              rw [hdecode]
              rfl
        _ = List.ofFn wordBytes := congrArg List.ofFn
            (PublicIndexCodec.encode_decode wordBytes)
        _ = bytes := ListFieldCodec.fixedBytes?_sound 8 bytes wordBytes hfixed

end AspisR1.PublicIndexListCodec

#print axioms AspisR1.PublicIndexListCodec.encode_length8
#print axioms AspisR1.PublicIndexListCodec.decode_encode
#print axioms AspisR1.PublicIndexListCodec.encode_of_decode

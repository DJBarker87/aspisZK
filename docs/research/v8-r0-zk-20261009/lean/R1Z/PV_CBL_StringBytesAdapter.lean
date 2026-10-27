import R1Z.PV_CBL_StringPushBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_StringBytesAdapter
set_option autoImplicit false
def encodeByte (b : UInt8) : U8 := U8.ofNatCore b.toNat (UInt8.toNat_lt b)
def decodeByte (b : U8) : UInt8 := UInt8.ofNat b.val
def encodeList (s : String) : List U8 := s.toByteArray.data.toList.map encodeByte
def encode (s : String) : Result (alloc.vec.Vec U8) :=
  let xs := encodeList s
  if h : xs.length ≤ Usize.max then ok ⟨xs,h⟩ else fail .maximumSizeExceeded
def decode (v : alloc.vec.Vec U8) : Result String :=
  match String.fromUTF8? (ByteArray.mk ((v.val.map decodeByte).toArray)) with
  | some s => ok s
  | none => fail .panic
def append (s : String) (t : Str) : Result String := do
  let v ← encode s
  let v ← PV_CBL_StringPushBytes.push_bytes_reference v t
  decode v
theorem byte_roundtrip (b : UInt8) : decodeByte (encodeByte b) = b := by
  simp [decodeByte,encodeByte]
theorem empty_encode : encode "" = ok (alloc.vec.Vec.new U8) := by
  simp [encode,encodeList,alloc.vec.Vec.new]
theorem empty_decode : decode (alloc.vec.Vec.new U8) = ok "" := rfl
#print axioms encodeByte
#print axioms decodeByte
#print axioms encodeList
#print axioms encode
#print axioms decode
#print axioms append
#print axioms byte_roundtrip
#print axioms empty_encode
#print axioms empty_decode
end R1Z.PV_CBL_StringBytesAdapter

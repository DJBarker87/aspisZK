import R1CanonicalByteAddress

/-! A total byte encoder with a separately stated in-range branch. -/
set_option autoImplicit false
namespace AspisR1.CanonicalByteHash

open FS2.Duplex
open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

def encode {L : Nat} (input : Bytes) : Addr L :=
  if h : input.length ≤ L then Addr.ofBytes input h else Addr.ofBytes [] (by simp)

def hashBytes {L : Nat} (H : Addr L → State) (input : Bytes) : State :=
  H (encode (L := L) input)

theorem encode_of_length {L : Nat} (input : Bytes) (h : input.length ≤ L) :
    encode (L := L) input = Addr.ofBytes input h := by
  simp [encode, h]

theorem encode_toBytes {L : Nat} (a : Addr L) :
    encode (L := L) a.toBytes = CanonicalByteAddress.normalize a := by
  rw [encode_of_length a.toBytes (CanonicalByteAddress.length_le a)]
  rfl

theorem toBytes_encode {L : Nat} (input : Bytes) (h : input.length ≤ L) :
    (encode (L := L) input).toBytes = input := by
  rw [encode_of_length input h]
  exact Addr.toBytes_ofBytes input h

theorem encode_canonical {L : Nat} (input : Bytes) :
    CanonicalByteAddress.Canonical (encode (L := L) input) := by
  by_cases h : input.length ≤ L
  · rw [encode_of_length input h]
    exact CanonicalByteAddress.canonical_ofBytes input h
  · rw [show encode (L := L) input = Addr.ofBytes [] (by simp) by simp [encode, h]]
    exact CanonicalByteAddress.canonical_ofBytes [] (by simp)

theorem hashBytes_of_length {L : Nat} (H : Addr L → State)
    (input : Bytes) (h : input.length ≤ L) :
    hashBytes H input = H (Addr.ofBytes input h) := by
  simp [hashBytes, encode_of_length input h]

theorem hashBytes_toBytes_canonical {L : Nat} (H : Addr L → State)
    (a : Addr L) (ha : CanonicalByteAddress.Canonical a) :
    hashBytes H a.toBytes = H a := by
  rw [hashBytes, encode_toBytes, ha]

#print axioms encode_of_length
#print axioms encode_toBytes
#print axioms toBytes_encode
#print axioms encode_canonical
#print axioms hashBytes_of_length
#print axioms hashBytes_toBytes_canonical

end AspisR1.CanonicalByteHash

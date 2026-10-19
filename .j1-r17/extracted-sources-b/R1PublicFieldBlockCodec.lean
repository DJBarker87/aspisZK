import R1ExactLeafFieldCodec
import R1FixedWidthDecoder

/-! Fixed-width sequences of exact M31 values used by the public index,
digest, and frontier models. This is a mathematical codec composition and
does not assert a Rust source correspondence. -/
set_option autoImplicit false

namespace AspisR1.PublicFieldBlockCodec

open AspisR1.ExactLeafFieldCodec
open AspisR1.FixedWidthDecoder

abbrev Byte := ExactLeafFieldCodec.Byte
abbrev M31 := ExactLeafFieldCodec.M31Exact
abbrev Digest := Fin 8 → M31
abbrev Frontier := Fin 20 → Digest

def encodeFields {n : Nat} (xs : Fin n → M31) : List Byte :=
  FixedWidthDecoder.encode ExactLeafFieldCodec.encodeM31 xs

def decodeFields (n : Nat) (bytes : List Byte) : Option (Fin n → M31) :=
  FixedWidthDecoder.decode ExactLeafFieldCodec.decodeM31 4 n bytes

theorem encodeFields_length {n : Nat} (xs : Fin n → M31) :
    (encodeFields xs).length = 4 * n := by
  induction n with
  | zero =>
      have hxs : xs = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp [encodeFields, FixedWidthDecoder.encode, hxs]
  | succ n ih =>
      let tail : Fin n → M31 := fun i => xs i.succ
      have hcons : Fin.cons (xs 0) tail = xs := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have henc : encodeFields xs = encodeM31 (xs 0) ++ encodeFields tail := by
        unfold encodeFields FixedWidthDecoder.encode
        rw [← hcons]
        simp [tail, List.ofFn_succ, List.flatMap_cons]
      rw [henc, List.length_append, ExactLeafFieldCodec.encodeM31_length, ih tail]
      omega

theorem decodeFields_encodeFields {n : Nat} (xs : Fin n → M31) :
    decodeFields n (encodeFields xs) = some xs := by
  exact FixedWidthDecoder.decode_encode ExactLeafFieldCodec.decodeM31
    ExactLeafFieldCodec.encodeM31 4 n xs
    ExactLeafFieldCodec.encodeM31_length ExactLeafFieldCodec.decodeM31_encodeM31

theorem encodeFields_of_decodeFields {n : Nat} (bytes : List Byte)
    (xs : Fin n → M31) (h : decodeFields n bytes = some xs) :
    encodeFields xs = bytes := by
  exact FixedWidthDecoder.encode_of_decode ExactLeafFieldCodec.decodeM31
    ExactLeafFieldCodec.encodeM31 4 n bytes xs h
    ExactLeafFieldCodec.encodeM31_of_decodeM31

def encodeDigest (digest : Digest) : List Byte := encodeFields digest

def decodeDigest (bytes : List Byte) : Option Digest := decodeFields 8 bytes

theorem encodeDigest_length (digest : Digest) :
    (encodeDigest digest).length = 32 := by
  simpa [encodeDigest] using (encodeFields_length digest)

theorem decodeDigest_encodeDigest (digest : Digest) :
    decodeDigest (encodeDigest digest) = some digest :=
  decodeFields_encodeFields digest

theorem encodeDigest_of_decodeDigest (bytes : List Byte) (digest : Digest)
    (h : decodeDigest bytes = some digest) : encodeDigest digest = bytes :=
  encodeFields_of_decodeFields bytes digest h

def encodeFrontier (frontier : Frontier) : List Byte :=
  FixedWidthDecoder.encode encodeDigest frontier

def decodeFrontier (bytes : List Byte) : Option Frontier :=
  FixedWidthDecoder.decode decodeDigest 32 20 bytes

theorem encodeFrontier_length (frontier : Frontier) :
    (encodeFrontier frontier).length = 640 := by
  unfold encodeFrontier FixedWidthDecoder.encode
  simp [List.length_flatMap, List.length_ofFn, encodeDigest_length]

theorem decodeFrontier_encodeFrontier (frontier : Frontier) :
    decodeFrontier (encodeFrontier frontier) = some frontier := by
  exact FixedWidthDecoder.decode_encode decodeDigest encodeDigest 32 20 frontier
    encodeDigest_length decodeDigest_encodeDigest

theorem encodeFrontier_of_decodeFrontier (bytes : List Byte) (frontier : Frontier)
    (h : decodeFrontier bytes = some frontier) : encodeFrontier frontier = bytes := by
  exact FixedWidthDecoder.encode_of_decode decodeDigest encodeDigest 32 20 bytes frontier h
    encodeDigest_of_decodeDigest

#print axioms encodeFields_length
#print axioms decodeFields_encodeFields
#print axioms encodeFields_of_decodeFields
#print axioms encodeDigest_length
#print axioms decodeDigest_encodeDigest
#print axioms encodeDigest_of_decodeDigest
#print axioms encodeFrontier_length
#print axioms decodeFrontier_encodeFrontier
#print axioms encodeFrontier_of_decodeFrontier

end AspisR1.PublicFieldBlockCodec

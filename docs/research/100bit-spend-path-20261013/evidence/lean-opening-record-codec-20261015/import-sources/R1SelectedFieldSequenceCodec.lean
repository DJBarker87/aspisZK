import R1SemanticCoefficientCodec
import R1FixedWidthDecodedSlices

/-! Generic fixed-width codecs for lists of strict low-field and wide-field
values. These wrappers reuse the checked element codecs and the structural
fixed-width parser; they do not assign a protocol row meaning. -/
set_option autoImplicit false

namespace AspisR1.SelectedFieldSequenceCodec

open AspisR1.FixedWidthDecoder
open AspisR1.FixedWidthDecodedSlices
open AspisR1.SemanticCoefficientCodec
open AspisR1.FoldedLeafCodec

abbrev Byte := AspisR1.RetainedFieldByteCodec.Byte
abbrev LowWide := AspisR1.SemanticCoefficientCodec.LowWide
abbrev Wide := AspisR1.FoldedLeafCodec.Wide

private theorem encode_length {B A : Type} (f : A → List B) (k n : Nat)
    (xs : Fin n → A) (hlen : ∀ a, (f a).length = k) :
    (AspisR1.FixedWidthDecoder.encode f xs).length = n * k := by
  induction n with
  | zero => simp [AspisR1.FixedWidthDecoder.encode]
  | succ n ih =>
      let tail : Fin n → A := fun i => xs i.succ
      have henc : AspisR1.FixedWidthDecoder.encode f xs =
          f (xs 0) ++ AspisR1.FixedWidthDecoder.encode f tail := by
        simp [AspisR1.FixedWidthDecoder.encode, tail,
          List.ofFn_succ, List.flatMap_cons]
      rw [henc, List.length_append, hlen (xs 0), ih tail]
      simp [Nat.succ_mul, Nat.add_comm]

def encodeLow {n : Nat} (xs : Fin n → LowWide) : List Byte :=
  AspisR1.FixedWidthDecoder.encode AspisR1.SemanticCoefficientCodec.encodeLow xs

def decodeLow (n : Nat) (bytes : List Byte) : Option (Fin n → LowWide) :=
  AspisR1.FixedWidthDecoder.decode AspisR1.SemanticCoefficientCodec.decodeLow 32 n bytes

theorem encodeLow_length {n : Nat} (xs : Fin n → LowWide) :
    (encodeLow xs).length = n * 32 := by
  exact encode_length AspisR1.SemanticCoefficientCodec.encodeLow 32 n xs
    AspisR1.SemanticCoefficientCodec.encodeLow_length

theorem decodeLow_encode {n : Nat} (xs : Fin n → LowWide) :
    decodeLow n (encodeLow xs) = some xs := by
  exact AspisR1.FixedWidthDecoder.decode_encode
    AspisR1.SemanticCoefficientCodec.decodeLow
    AspisR1.SemanticCoefficientCodec.encodeLow 32 n xs
    AspisR1.SemanticCoefficientCodec.encodeLow_length
    AspisR1.SemanticCoefficientCodec.decodeLow_encode

theorem encodeLow_of_decode {n : Nat} (bytes : List Byte)
    (xs : Fin n → LowWide) (h : decodeLow n bytes = some xs) :
    encodeLow xs = bytes := by
  exact AspisR1.FixedWidthDecoder.encode_of_decode
    AspisR1.SemanticCoefficientCodec.decodeLow
    AspisR1.SemanticCoefficientCodec.encodeLow 32 n bytes xs h
    AspisR1.SemanticCoefficientCodec.encodeLow_of_decode

theorem decodeLow_eq_some_iff {n : Nat} (bytes : List Byte)
    (xs : Fin n → LowWide) :
    decodeLow n bytes = some xs ↔
      bytes.length = n * 32 ∧
        ∀ i : Fin n,
          AspisR1.SemanticCoefficientCodec.decodeLow
            ((bytes.drop (32 * i.val)).take 32) = some (xs i) := by
  exact AspisR1.FixedWidthDecodedSlices.decode_eq_some_iff
    AspisR1.SemanticCoefficientCodec.decodeLow
    AspisR1.SemanticCoefficientCodec.encodeLow 32 n bytes xs
    AspisR1.SemanticCoefficientCodec.encodeLow_length
    AspisR1.SemanticCoefficientCodec.decodeLow_encode
    AspisR1.SemanticCoefficientCodec.encodeLow_of_decode

def encodeWide {n : Nat} (xs : Fin n → Wide) : List Byte :=
  AspisR1.FixedWidthDecoder.encode AspisR1.FoldedLeafCodec.encodeWide xs

def decodeWide (n : Nat) (bytes : List Byte) : Option (Fin n → Wide) :=
  AspisR1.FixedWidthDecoder.decode AspisR1.FoldedLeafCodec.decodeWide 32 n bytes

theorem encodeWide_length {n : Nat} (xs : Fin n → Wide) :
    (encodeWide xs).length = n * 32 := by
  exact encode_length AspisR1.FoldedLeafCodec.encodeWide 32 n xs
    AspisR1.FoldedLeafCodec.encodeWide_length

theorem decodeWide_encode {n : Nat} (xs : Fin n → Wide) :
    decodeWide n (encodeWide xs) = some xs := by
  exact AspisR1.FixedWidthDecoder.decode_encode
    AspisR1.FoldedLeafCodec.decodeWide
    AspisR1.FoldedLeafCodec.encodeWide 32 n xs
    AspisR1.FoldedLeafCodec.encodeWide_length
    AspisR1.FoldedLeafCodec.decodeWide_encode

theorem encodeWide_of_decode {n : Nat} (bytes : List Byte)
    (xs : Fin n → Wide) (h : decodeWide n bytes = some xs) :
    encodeWide xs = bytes := by
  exact AspisR1.FixedWidthDecoder.encode_of_decode
    AspisR1.FoldedLeafCodec.decodeWide
    AspisR1.FoldedLeafCodec.encodeWide 32 n bytes xs h
    AspisR1.FoldedLeafCodec.encodeWide_of_decode

theorem decodeWide_eq_some_iff {n : Nat} (bytes : List Byte)
    (xs : Fin n → Wide) :
    decodeWide n bytes = some xs ↔
      bytes.length = n * 32 ∧
        ∀ i : Fin n,
          AspisR1.FoldedLeafCodec.decodeWide
            ((bytes.drop (32 * i.val)).take 32) = some (xs i) := by
  exact AspisR1.FixedWidthDecodedSlices.decode_eq_some_iff
    AspisR1.FoldedLeafCodec.decodeWide
    AspisR1.FoldedLeafCodec.encodeWide 32 n bytes xs
    AspisR1.FoldedLeafCodec.encodeWide_length
    AspisR1.FoldedLeafCodec.decodeWide_encode
    AspisR1.FoldedLeafCodec.encodeWide_of_decode

#print axioms encodeLow_length
#print axioms decodeLow_encode
#print axioms encodeLow_of_decode
#print axioms decodeLow_eq_some_iff
#print axioms encodeWide_length
#print axioms decodeWide_encode
#print axioms encodeWide_of_decode
#print axioms decodeWide_eq_some_iff

end AspisR1.SelectedFieldSequenceCodec

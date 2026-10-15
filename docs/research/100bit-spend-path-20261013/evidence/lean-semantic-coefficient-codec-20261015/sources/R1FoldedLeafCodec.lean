import R1FixedWidthDecoder
import R1FixedWidthDecodedSlices
import R1StrictWideByteCodec
import R1WideExactLimbCodec
import R1ListFieldCodec

/-! Exact list codec for the four WideExact values in a folded Merkle leaf.
This is a byte-model statement and does not identify the folded leaf with C2. -/
set_option autoImplicit false

namespace AspisR1.FoldedLeafCodec

open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.WideExactLimbCodec
open AspisWideTower

abbrev Wide := WideExact
abbrev Folded := Fin 4 → Wide

def encodeWide (x : Wide) : List Byte :=
  List.ofFn (encodeWideLE (pairExactEquiv.symm x))

def decodeWide (bytes : List Byte) : Option Wide :=
  ((fixedBytes? 32 bytes).bind decodeWideLE).map pairExactEquiv

theorem encodeWide_length (x : Wide) : (encodeWide x).length = 32 := by
  simp [encodeWide, List.length_ofFn]

theorem decodeWide_encode (x : Wide) : decodeWide (encodeWide x) = some x := by
  unfold decodeWide encodeWide
  rw [AspisR1.ListFieldCodec.fixedBytes?_ofFn]
  simp [decodeWideLE_encodeWideLE]

theorem encodeWide_of_decode (bytes : List Byte) (x : Wide)
    (h : decodeWide bytes = some x) : encodeWide x = bytes := by
  unfold decodeWide at h
  cases hf : fixedBytes? 32 bytes with
  | none => simp [hf] at h
  | some bs =>
      cases hd : decodeWideLE bs with
      | none => simp [decodeWide, hf, hd] at h
      | some limbs =>
          have hx : pairExactEquiv limbs = x := by
            simpa [decodeWide, hf, hd] using h
          have hlimbs : limbs = pairExactEquiv.symm x := by
            apply pairExactEquiv.injective
            simpa using hx
          subst limbs
          have hbytes := AspisR1.ListFieldCodec.fixedBytes?_sound 32 bytes bs hf
          have henc := encodeWideLE_of_decodeWideLE bs
            (pairExactEquiv.symm x) (by simpa [hd])
          change List.ofFn (encodeWideLE (pairExactEquiv.symm x)) = bytes
          rw [henc, ← hbytes]

theorem decodeWide_eq_some_iff (bytes : List Byte) (x : Wide) :
    decodeWide bytes = some x ↔ encodeWide x = bytes := by
  constructor
  · exact encodeWide_of_decode bytes x
  · intro h
    rw [← h]
    exact decodeWide_encode x

def encodeFolded (xs : Folded) : List Byte :=
  AspisR1.FixedWidthDecoder.encode encodeWide xs

def decodeFolded (bytes : List Byte) : Option Folded :=
  AspisR1.FixedWidthDecoder.decode decodeWide 32 4 bytes

theorem encodeFolded_length (xs : Folded) : (encodeFolded xs).length = 128 := by
  unfold encodeFolded AspisR1.FixedWidthDecoder.encode
  simp [List.length_flatMap, List.length_ofFn, encodeWide_length]

theorem decodeFolded_encode (xs : Folded) : decodeFolded (encodeFolded xs) = some xs := by
  exact AspisR1.FixedWidthDecoder.decode_encode decodeWide encodeWide 32 4 xs
    encodeWide_length decodeWide_encode

theorem encodeFolded_of_decode (bytes : List Byte) (xs : Folded)
    (h : decodeFolded bytes = some xs) : encodeFolded xs = bytes := by
  exact AspisR1.FixedWidthDecoder.encode_of_decode decodeWide encodeWide 32 4
    bytes xs h encodeWide_of_decode

theorem decodeFolded_eq_some_iff (bytes : List Byte) (xs : Folded) :
    decodeFolded bytes = some xs ↔
      bytes.length = 128 ∧
        ∀ i : Fin 4, decodeWide ((bytes.drop (32 * i.val)).take 32) = some (xs i) := by
  exact AspisR1.FixedWidthDecodedSlices.decode_eq_some_iff decodeWide encodeWide
    32 4 bytes xs encodeWide_length decodeWide_encode encodeWide_of_decode

theorem decodeFolded_slot (bytes : List Byte) (xs : Folded)
    (h : decodeFolded bytes = some xs) (i : Fin 4) :
    decodeWide ((bytes.drop (32 * i.val)).take 32) = some (xs i) :=
  (decodeFolded_eq_some_iff bytes xs).mp h |>.2 i

#print axioms encodeWide_length
#print axioms decodeWide_encode
#print axioms encodeWide_of_decode
#print axioms decodeWide_eq_some_iff
#print axioms encodeFolded_length
#print axioms decodeFolded_encode
#print axioms encodeFolded_of_decode
#print axioms decodeFolded_eq_some_iff
#print axioms decodeFolded_slot

end AspisR1.FoldedLeafCodec

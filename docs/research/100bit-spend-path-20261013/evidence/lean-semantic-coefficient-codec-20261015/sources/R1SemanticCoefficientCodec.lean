import R1FoldedLeafCodec
import R1FixedWidthDecoder
import R1FixedWidthDecodedSlices

/-! Strict byte codec for one base-slice WideExact value and one 28-value
semantic coefficient payload. This is a payload codec only: it does not parse
record headers or identify a source caller. -/
set_option autoImplicit false

namespace AspisR1.SemanticCoefficientCodec

open AspisR1.FoldedLeafCodec
open AspisR1.FixedWidthDecoder
open AspisWideTower
open Polynomial

abbrev Byte := AspisR1.RetainedFieldByteCodec.Byte

/-- Wide values whose upper quadratic coordinate is zero. -/
abbrev LowWide := { x : WideExact // x.im = 0 }

def encodeLow (x : LowWide) : List Byte := encodeWide x.val

def decodeLow (bytes : List Byte) : Option LowWide :=
  (decodeWide bytes).bind fun x =>
    if h : x.im = 0 then some ⟨x, h⟩ else none

theorem encodeLow_length (x : LowWide) : (encodeLow x).length = 32 :=
  encodeWide_length x.val

theorem decodeLow_encode (x : LowWide) : decodeLow (encodeLow x) = some x := by
  simp [decodeLow, encodeLow, decodeWide_encode, x.property]

theorem encodeLow_of_decode (bytes : List Byte) (x : LowWide)
    (h : decodeLow bytes = some x) : encodeLow x = bytes := by
  unfold decodeLow at h
  cases hd : decodeWide bytes with
  | none => simp [hd] at h
  | some value =>
      by_cases him : value.im = 0
      · have hsub : (⟨value, him⟩ : LowWide) = x := by
          simpa [decodeLow, hd, him] using h
        have hv : value = x.val := congrArg Subtype.val hsub
        have hd' : decodeWide bytes = some x.val := by rw [← hv]; exact hd
        simpa [encodeLow] using encodeWide_of_decode bytes x.val hd'
      · simp [hd, him] at h

theorem decodeLow_eq_some_iff (bytes : List Byte) (x : LowWide) :
    decodeLow bytes = some x ↔ encodeLow x = bytes := by
  constructor
  · exact encodeLow_of_decode bytes x
  · intro h
    rw [← h]
    exact decodeLow_encode x

abbrev Coefficients := Fin 28 → LowWide

def encodeCoefficients (xs : Coefficients) : List Byte :=
  FixedWidthDecoder.encode encodeLow xs

def decodeCoefficients (bytes : List Byte) : Option Coefficients :=
  FixedWidthDecoder.decode decodeLow 32 28 bytes

theorem encodeCoefficients_length (xs : Coefficients) :
    (encodeCoefficients xs).length = 896 := by
  unfold encodeCoefficients FixedWidthDecoder.encode
  simp [List.length_flatMap, List.length_ofFn, encodeLow_length]

theorem decodeCoefficients_encode (xs : Coefficients) :
    decodeCoefficients (encodeCoefficients xs) = some xs :=
  FixedWidthDecoder.decode_encode decodeLow encodeLow 32 28 xs
    encodeLow_length decodeLow_encode

theorem encodeCoefficients_of_decode (bytes : List Byte) (xs : Coefficients)
    (h : decodeCoefficients bytes = some xs) : encodeCoefficients xs = bytes :=
  FixedWidthDecoder.encode_of_decode decodeLow encodeLow 32 28 bytes xs h
    encodeLow_of_decode

theorem decodeCoefficients_eq_some_iff (bytes : List Byte) (xs : Coefficients) :
    decodeCoefficients bytes = some xs ↔
      bytes.length = 896 ∧ ∀ i : Fin 28,
        decodeLow ((bytes.drop (32 * i.val)).take 32) = some (xs i) := by
  exact FixedWidthDecodedSlices.decode_eq_some_iff decodeLow encodeLow 32 28
    bytes xs encodeLow_length decodeLow_encode encodeLow_of_decode

theorem decodeCoefficients_slot (bytes : List Byte) (xs : Coefficients)
    (h : decodeCoefficients bytes = some xs) (i : Fin 28) :
    decodeLow ((bytes.drop (32 * i.val)).take 32) = some (xs i) :=
  (decodeCoefficients_eq_some_iff bytes xs).mp h |>.2 i

/-- Polynomial with the decoded coefficients in ascending monomial order. -/
noncomputable def polynomial (xs : Coefficients) : Polynomial WideExact :=
  ∑ i : Fin 28, C (xs i).val * X ^ i.val

theorem polynomial_natDegree_le (xs : Coefficients) :
    (polynomial xs).natDegree ≤ 27 := by
  unfold polynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

#print axioms encodeLow_length
#print axioms decodeLow_encode
#print axioms encodeLow_of_decode
#print axioms decodeLow_eq_some_iff
#print axioms encodeCoefficients_length
#print axioms decodeCoefficients_encode
#print axioms encodeCoefficients_of_decode
#print axioms decodeCoefficients_eq_some_iff
#print axioms decodeCoefficients_slot
#print axioms polynomial_natDegree_le

end AspisR1.SemanticCoefficientCodec

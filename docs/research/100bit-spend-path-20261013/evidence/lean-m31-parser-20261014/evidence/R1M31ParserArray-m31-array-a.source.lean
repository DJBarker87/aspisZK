import R1M31ParserCanonicality

/-! Lift the fixed `Fin 4 → Fin 256` M31 parser contract to every Aeneas
four-byte array using the existing U8/byte roundtrip. -/
set_option autoImplicit false

namespace AspisR1.M31ParserArray

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.M31ParserRefinement
open AspisR1.M31ParserCanonicality

def arrayBytes (arr : Array U8 4#usize) : WordBytes :=
  fun i => AspisV8R19.SqueezeOracleBridge.decodeByte
    (arr.val[i.val]'(by have hlen := arr.property; omega))

theorem wordArray_arrayBytes (arr : Array U8 4#usize) :
    wordArray (arrayBytes arr) = arr := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [wordArray, arrayBytes, Array.make, arr.property]
  · intro i hi hj
    have hi4 : i < 4 := by simpa using hj
    interval_cases i <;>
      simp [wordArray, arrayBytes, Array.make,
        AspisV8R19.SqueezeOracleBridge.word_roundtrip]

theorem parser_refines_array (arr : Array U8 4#usize) :
    AspisR1M31Parser.field.M31.from_le_bytes arr =
      Result.ok ((decodeM31LE (arrayBytes arr)).map valueToU32) := by
  calc
    AspisR1M31Parser.field.M31.from_le_bytes arr =
        AspisR1M31Parser.field.M31.from_le_bytes (wordArray (arrayBytes arr)) :=
      congrArg AspisR1M31Parser.field.M31.from_le_bytes
        (wordArray_arrayBytes arr).symm
    _ = Result.ok ((decodeM31LE (arrayBytes arr)).map valueToU32) :=
      from_le_bytes_refines (arrayBytes arr)

theorem successful_array_value_canonical (arr : Array U8 4#usize)
    (value : U32)
    (hparsed :
      AspisR1M31Parser.field.M31.from_le_bytes arr =
        Result.ok (some value)) :
    value.val < m31Modulus ∧
      value.val = (decodeWordLE (arrayBytes arr)).val := by
  apply successful_value_canonical (arrayBytes arr) value
  simpa only [wordArray_arrayBytes arr] using hparsed

#print axioms wordArray_arrayBytes
#print axioms parser_refines_array
#print axioms successful_array_value_canonical

end AspisR1.M31ParserArray

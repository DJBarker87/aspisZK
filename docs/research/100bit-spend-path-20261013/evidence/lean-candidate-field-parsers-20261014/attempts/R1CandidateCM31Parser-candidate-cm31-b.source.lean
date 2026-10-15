import R1CandidateParserSupport
import R1ParserArraySlice

/-! All-input bridge from the retained candidate CM31 parser to two successive
M31 decodings. This is parser plumbing only; no canonicality premise is used. -/
set_option autoImplicit false

namespace AspisR1.CandidateCM31Parser

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.M31ParserRefinement

/-- First four-byte half of an eight-byte array. -/
def half0 (arr : Array U8 8#usize) : Array U8 4#usize :=
  AspisR1.ParserArraySlice.segment arr 0#usize 4#usize (by decide)

/-- Second four-byte half of an eight-byte array. -/
def half1 (arr : Array U8 8#usize) : Array U8 4#usize :=
  AspisR1.ParserArraySlice.segment arr 4#usize 4#usize (by decide)

/-- Candidate mathematical CM31 decoding, preserving each M31 rejection. -/
def decodeCM31 (arr : Array U8 8#usize) : Option AspisR1CandidateParser.field.CM31 := do
  let a ← decodeM31LE (AspisR1.M31ParserArray.arrayBytes (half0 arr))
  let b ← decodeM31LE (AspisR1.M31ParserArray.arrayBytes (half1 arr))
  some ⟨valueToU32 a, valueToU32 b⟩

theorem from_le_bytes_refines (arr : Array U8 8#usize) :
    AspisR1CandidateParser.field.CM31.from_le_bytes (Array.to_slice arr) =
      Result.ok (decodeCM31 arr) := by
  have hslice0 := AspisR1.ParserArraySlice.slice_segment arr
    0#usize 4#usize (by decide) 4#usize (by decide)
  have hslice1 := AspisR1.ParserArraySlice.slice_segment arr
    4#usize 4#usize (by decide) 8#usize (by decide)
  change _ = Result.ok (Array.to_slice (half0 arr)) at hslice0
  change _ = Result.ok (Array.to_slice (half1 arr)) at hslice1
  have h0 := AspisR1.CandidateParserSupport.parser_refines_array (half0 arr)
  have h1 := AspisR1.CandidateParserSupport.parser_refines_array (half1 arr)
  cases hx : decodeM31LE (AspisR1.M31ParserArray.arrayBytes (half0 arr)) <;>
    cases hy : decodeM31LE (AspisR1.M31ParserArray.arrayBytes (half1 arr)) <;>
    simp [AspisR1CandidateParser.field.CM31.from_le_bytes,
      hslice0, hslice1,
      AspisV8R19.SamplerWordRead.conversion_success,
      h0, h1,
      AspisR1.CandidateParserSupport.branch_none,
      AspisR1.CandidateParserSupport.branch_some,
      AspisR1.CandidateParserSupport.residual_complete,
      decodeCM31, hx, hy]

#print axioms half0
#print axioms half1
#print axioms decodeCM31
#print axioms from_le_bytes_refines

end AspisR1.CandidateCM31Parser

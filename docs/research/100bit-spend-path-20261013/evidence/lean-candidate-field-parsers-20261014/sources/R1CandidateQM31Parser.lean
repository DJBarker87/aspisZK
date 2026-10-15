import R1CandidateCM31Parser
import R1ParserArraySlice
import R1CandidateParserSupport

/-! The candidate QM31 parser is related to two strict eight-byte CM31
    decodes over the checked halves of a fixed sixteen-byte array. -/
set_option autoImplicit false

namespace AspisR1.CandidateQM31Parser

open Aeneas Aeneas.Std Result

def half0 (arr : Array U8 16#usize) : Array U8 8#usize :=
  AspisR1.ParserArraySlice.segment arr 0#usize 8#usize (by decide)

def half1 (arr : Array U8 16#usize) : Array U8 8#usize :=
  AspisR1.ParserArraySlice.segment arr 8#usize 8#usize (by decide)

def decodeQM31 (arr : Array U8 16#usize) :
    Option AspisR1CandidateParser.field.QM31 := do
  let c0 ← AspisR1.CandidateCM31Parser.decodeCM31 (half0 arr)
  let c1 ← AspisR1.CandidateCM31Parser.decodeCM31 (half1 arr)
  some { c0 := c0, c1 := c1 }

theorem from_le_bytes_refines (arr : Array U8 16#usize) :
    AspisR1CandidateParser.field.QM31.from_le_bytes (Array.to_slice arr) =
      Result.ok (decodeQM31 arr) := by
  have h0slice :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) (Array.to_slice arr)
        { start := 0#usize, «end» := 8#usize } =
        Result.ok (Array.to_slice (half0 arr)) := by
    simpa [half0] using
      AspisR1.ParserArraySlice.slice_segment arr 0#usize 8#usize
        (by decide) 8#usize (by decide)
  have h1slice :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) (Array.to_slice arr)
        { start := 8#usize, «end» := 16#usize } =
        Result.ok (Array.to_slice (half1 arr)) := by
    simpa [half1] using
      AspisR1.ParserArraySlice.slice_segment arr 8#usize 8#usize
        (by decide) 16#usize (by decide)
  have h0 :
      AspisR1CandidateParser.field.CM31.from_le_bytes
        (Array.to_slice (half0 arr)) =
        Result.ok (AspisR1.CandidateCM31Parser.decodeCM31 (half0 arr)) :=
    AspisR1.CandidateCM31Parser.from_le_bytes_refines (half0 arr)
  have h1 :
      AspisR1CandidateParser.field.CM31.from_le_bytes
        (Array.to_slice (half1 arr)) =
        Result.ok (AspisR1.CandidateCM31Parser.decodeCM31 (half1 arr)) :=
    AspisR1.CandidateCM31Parser.from_le_bytes_refines (half1 arr)
  cases hx : AspisR1.CandidateCM31Parser.decodeCM31 (half0 arr) <;>
    cases hy : AspisR1.CandidateCM31Parser.decodeCM31 (half1 arr) <;>
    simp [AspisR1CandidateParser.field.QM31.from_le_bytes,
      h0slice, h1slice, h0, h1, decodeQM31, hx, hy,
      AspisR1.CandidateParserSupport.branch_none,
      AspisR1.CandidateParserSupport.branch_some,
      AspisR1.CandidateParserSupport.residual_complete]

#print axioms from_le_bytes_refines

end AspisR1.CandidateQM31Parser

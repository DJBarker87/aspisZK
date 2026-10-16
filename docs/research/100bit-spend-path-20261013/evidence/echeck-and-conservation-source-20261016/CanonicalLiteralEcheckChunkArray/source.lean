import CanonicalLiteralEcheckRound1Success
import UnrolledWideParserRefinement
import UnrolledWideByteReads

/-! A successful generated parser call gives a length-32 array representation
for each consumed slice chunk. This uses the retained proof that the current
unrolled parser agrees with its fixed-byte source parser. -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralEcheckChunkArray
open Aeneas Aeneas.Std Result
open AspisR1.CanonicalLiteralEcheckRound1Success

abbrev CandidateWide := AspisR1CandidateParser.field.wide_exact.WideExact

theorem slice_success_array (chunk : Slice U8) (w : CandidateWide)
    (h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
      chunk = ok (some w)) :
    ∃ arr : Array U8 32#usize,
      Array.to_slice arr = chunk ∧
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
        (Array.to_slice arr) = ok (some w) := by
  have hsourceEq := AspisR1.UnrolledWideParserRefinement.source_eq_half_parser chunk
  have hhalf : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
      chunk = ok (some w) := by
    rw [← hsourceEq]
    exact h
  have hlen : chunk.val.length = 32 := by
    by_contra hn
    have hnone := AspisR1.UnrolledWideByteReads.wrong_length chunk hn
    rw [hsourceEq] at hnone
    rw [hhalf] at hnone
    cases hnone
  let arr : Array U8 32#usize := ⟨chunk.val, by simpa using hlen⟩
  have hs : Array.to_slice arr = chunk := by cases chunk; rfl
  refine ⟨arr, hs, ?_⟩
  rw [hs]
  exact h

#print axioms slice_success_array

end AspisR1.CanonicalLiteralEcheckChunkArray

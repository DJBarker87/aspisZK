import R1CandidateWideParserSource
import R1CandidateStrictQM31Parser
import R1CandidateFieldCanonicality
import R1WideParserArrayHalves
import R1StrictWideByteCodec

/-! Strict decoding for the isolated two-half WideExact parser. The narrow
parser proof and byte decoder are reused. No canonical-input premise is used.
The extracted candidate remains separate from the current runtime source. -/
set_option autoImplicit false

namespace AspisR1.CandidateWideParserRefinement

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec
open AspisR1.WideParserArrayHalves

abbrev Wide := AspisR1CandidateParser.field.wide_exact.WideExact

def limbsToCandidate (limbs : WideLimbs) : Wide :=
  { c0 := AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs.1,
    c1 := AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs.2 }

theorem wrong_length (bytes : Slice U8) (h : bytes.val.length ≠ 32) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes bytes =
      Result.ok none := by
  have hlen : Slice.len bytes ≠ 32#usize := by
    intro heq
    apply h
    have hv := congrArg UScalar.val heq
    simpa [Slice.len, Slice.length] using hv
  simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes,
    AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN, hlen]

theorem source_refines (arr : Array U8 32#usize) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
        (Array.to_slice arr) =
      Result.ok ((decodeWideLE (arrayBytes32 arr)).map limbsToCandidate) := by
  have hlen : Slice.len (Array.to_slice arr) = 32#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice, arr.property]
  have h0 : AspisR1CandidateParser.field.QM31.from_le_bytes
      (Array.to_slice (half0 arr)) =
        Result.ok ((decodeQM31LE (lowBytes (arrayBytes32 arr))).map
          AspisR1.CandidateStrictQM31Parser.limbsToCandidate) := by
    have h := AspisR1.CandidateStrictQM31Parser.source_refines (half0 arr)
    rw [half0_bytes] at h
    exact h
  have h1 : AspisR1CandidateParser.field.QM31.from_le_bytes
      (Array.to_slice (half1 arr)) =
        Result.ok ((decodeQM31LE (highBytes (arrayBytes32 arr))).map
          AspisR1.CandidateStrictQM31Parser.limbsToCandidate) := by
    have h := AspisR1.CandidateStrictQM31Parser.source_refines (half1 arr)
    rw [half1_bytes] at h
    exact h
  cases hx : decodeQM31LE (lowBytes (arrayBytes32 arr)) <;>
    cases hy : decodeQM31LE (highBytes (arrayBytes32 arr)) <;>
    simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes,
      AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN,
      hlen, slice_half0, slice_half1, h0, h1, hx, hy, decodeWideLE,
      limbsToCandidate, AspisR1.CandidateParserSupport.branch_none,
      AspisR1.CandidateParserSupport.branch_some,
      AspisR1.CandidateParserSupport.residual_complete]

#print axioms wrong_length
#print axioms source_refines

end AspisR1.CandidateWideParserRefinement

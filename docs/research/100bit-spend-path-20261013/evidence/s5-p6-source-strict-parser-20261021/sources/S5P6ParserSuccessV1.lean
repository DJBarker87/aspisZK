import UnrolledWideParserRefinement
import R1StrictWideByteCodec

set_option autoImplicit false

namespace AspisR1S5P6ParserSuccessV1

open Aeneas Aeneas.Std Result

/-- A strict encoding is accepted by the extracted fixed-width wide parser. -/
theorem parser_success_of_strict_encoding
    (arr : Array U8 32#usize)
    (limbs : AspisR1.StrictWideByteCodec.WideLimbs)
    (hbytes : AspisR1.WideParserArrayHalves.arrayBytes32 arr =
      AspisR1.StrictWideByteCodec.encodeWideLE limbs) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
      (Array.to_slice arr) =
      .ok (some (AspisR1.CandidateWideParserRefinement.limbsToCandidate limbs)) := by
  rw [AspisR1.UnrolledWideParserRefinement.source_refines, hbytes]
  simp [AspisR1.StrictWideByteCodec.decodeWideLE_encodeWideLE]

#print axioms parser_success_of_strict_encoding

end AspisR1S5P6ParserSuccessV1

import R1WideParserArrayHalves
import R1StrictWideByteCodec
import R1WideExactLimbCodec
import R1CandidateWideParserSource
import R1CandidateWideParserRefinement
import R1CandidateWideParserContracts

/-! Frozen focused checkpoint for the six-module candidate WideExact parser
   batch. This file adds no declarations beyond the requested axiom audit. -/

#print axioms AspisR1.WideParserArrayHalves.slice_half0
#print axioms AspisR1.WideParserArrayHalves.slice_half1
#print axioms AspisR1.WideParserArrayHalves.half0_bytes
#print axioms AspisR1.WideParserArrayHalves.half1_bytes

#print axioms AspisR1.StrictWideByteCodec.decodeWideLE_encodeWideLE
#print axioms AspisR1.StrictWideByteCodec.encodeWideLE_of_decodeWideLE
#print axioms AspisR1.StrictWideByteCodec.successful_halves

#print axioms AspisR1.WideExactLimbCodec.pairExactEquiv_apply
#print axioms AspisR1.WideExactLimbCodec.pairExactEquiv_injective
#print axioms AspisR1.WideExactLimbCodec.pairToExact_eq_digitsField

#print axioms AspisR1CandidateParser.field.wide_exact.WideExact
#print axioms AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN
#print axioms AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
#print axioms AspisR1CandidateParser.parse_wide_exact_probe

#print axioms AspisR1.CandidateWideParserRefinement.wrong_length
#print axioms AspisR1.CandidateWideParserRefinement.source_refines

#print axioms AspisR1.CandidateWideParserContracts.total
#print axioms AspisR1.CandidateWideParserContracts.fixed_success
#print axioms AspisR1.CandidateWideParserContracts.slice_success_canonical

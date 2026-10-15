import UnrolledWideParserRefinement
import R1WideExactLimbCodec

/-! Frozen audit of the unrolled Wide parser refinement and its selected
byte, limb, and exact-field predecessor facts. -/

#print axioms AspisR1.UnrolledWideParserRefinement.limbs_refine
#print axioms AspisR1.UnrolledWideParserRefinement.source_refines
#print axioms AspisR1.UnrolledWideParserRefinement.source_eq_half_parser
#print axioms AspisR1.UnrolledWideParserRefinement.total
#print axioms AspisR1.UnrolledWideParserRefinement.slice_success_canonical
#print axioms AspisR1.UnrolledWideParserRefinement.fixed_success

#print axioms AspisR1.UnrolledWideByteReads.index_array32
#print axioms AspisR1.UnrolledWideByteReads.wrong_length
#print axioms AspisR1.UnrolledWideByteReads.fixed_reads

#print axioms AspisR1.UnrolledWideLimbChecks.from_limbs_make

#print axioms AspisR1.WideExactLimbCodec.pairToExact_eq_digitsField
#print axioms AspisR1.StrictWideByteCodec.encodeWideLE_of_decodeWideLE

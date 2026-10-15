import R1CandidateFieldCanonicality

/-! Focused combined audit of the isolated parser candidate. The generated
code is checked with retained Option support, canonical-decoder refinements,
and arbitrary fixed-length arrays. Runtime adoption and SBF cost are separate. -/

#print axioms AspisR1.ParserArraySlice.slice_segment
#print axioms AspisR1.CandidateParserSupport.branch_none
#print axioms AspisR1.CandidateParserSupport.branch_some
#print axioms AspisR1.CandidateParserSupport.residual_complete
#print axioms AspisR1.CandidateParserSupport.m31_from_le_bytes_eq_extracted
#print axioms AspisR1.CandidateParserSupport.parser_refines_array
#print axioms AspisR1.CandidateCM31Parser.from_le_bytes_refines
#print axioms AspisR1.CandidateQM31Parser.from_le_bytes_refines
#print axioms AspisR1.CandidateFieldCanonicality.decodeCM31_success_canonical
#print axioms AspisR1.CandidateFieldCanonicality.source_cm31_success_canonical
#print axioms AspisR1.CandidateFieldCanonicality.decodeQM31_success_canonical
#print axioms AspisR1.CandidateFieldCanonicality.source_qm31_success_canonical

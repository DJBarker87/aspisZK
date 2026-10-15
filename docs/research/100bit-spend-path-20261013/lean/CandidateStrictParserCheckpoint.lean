import R1CandidateStrictQM31Parser
import R1CandidateFieldCanonicality

/-! Focused audit of the candidate parser's exact strict-codec and canonicality
connections. This checkpoint introduces no protocol-security premise. -/
set_option autoImplicit false

#print axioms AspisR1.CandidateParserByteOrder.half00_bytes
#print axioms AspisR1.CandidateParserByteOrder.half10_bytes
#print axioms AspisR1.CandidateParserByteOrder.half01_bytes
#print axioms AspisR1.CandidateParserByteOrder.half11_bytes
#print axioms AspisR1.CandidateStrictQM31Parser.decoder_refines
#print axioms AspisR1.CandidateStrictQM31Parser.source_refines
#print axioms AspisR1.CandidateFieldCanonicality.decodeCM31_success_canonical
#print axioms AspisR1.CandidateFieldCanonicality.source_cm31_success_canonical
#print axioms AspisR1.CandidateFieldCanonicality.decodeQM31_success_canonical
#print axioms AspisR1.CandidateFieldCanonicality.source_qm31_success_canonical
#print axioms AspisR1.RetainedFieldByteCodec.decodeQM31LE_encodeQM31LE
#print axioms AspisR1.RetainedFieldByteCodec.encodeQM31LE_of_decodeQM31LE

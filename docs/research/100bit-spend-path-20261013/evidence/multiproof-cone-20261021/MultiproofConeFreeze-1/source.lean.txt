import MultiproofConeCodec
import MultiproofConeHeader
import MultiproofConeWordScan
import MultiproofConeEndian
import MultiproofConeLeaf
import MultiproofConeHeight
import OraclePortFrozenOrderHeadline

/-! Focused compatibility/axioms audit. There is deliberately no new
AcceptedRunJoin declaration: the concrete row/parser/caller joins remain open. -/
#print axioms AspisR1.MultiproofConeCodec.canonical_word_total
#print axioms AspisR1.MultiproofConeCodec.row_shape_total
#print axioms AspisR1.MultiproofConeCodec.expand_chunk_total
#print axioms AspisR1.MultiproofConeHeader.header_total
#print axioms AspisR1.MultiproofConeWordScan.words_total
#print axioms AspisR1.MultiproofConeEndian.strict_word_iff
#print axioms AspisR1.MultiproofConeEndian.little_four
#print axioms AspisR1.MultiproofConeLeaf.digest_eq_total
#print axioms AspisR1.MultiproofConeLeaf.digest_eq_spec
#print axioms AspisR1.MultiproofConeLeaf.leaf_step_total
#print axioms AspisR1.MultiproofConeHeight.height_total
#print axioms MultiproofConeRef.reference.verify_owned
#print axioms MultiproofParserRef.parser_reference.parse
#print axioms AspisR1.OraclePortHeadlineFrozen.final_soundness

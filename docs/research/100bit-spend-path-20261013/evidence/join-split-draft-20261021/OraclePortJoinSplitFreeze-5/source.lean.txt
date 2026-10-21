import OraclePortJoinSplitHeadline
import OraclePortJoinSplitOrdering
import OraclePortJoinSplitS2
import OraclePortJoinSplitS7
import OraclePortJoinSplitS8
import OraclePortJoinSplitR17
import OraclePortJoinSplitR22

/-! Final compatible main import/axioms audit. ASQ8 is audited separately:
the existing AspisR20Request.Types and AspisR1AdapterReconstruct.Types export
the same generated discriminant instance. No existing module is modified.
Historical caches remain subject to the coherent frozen release replay. -/
#print axioms AspisR1.OraclePortJoinSplit.executionJoin_of_cones
#print axioms AspisR1.OraclePortJoinSplitDecision.executionJoin
#print axioms AspisR1.OraclePortJoinSplitHeadline.final_soundness
#print axioms AspisR1.OraclePortJoinSplitHeadline.per_query
#print axioms AspisR1.OraclePortJoinSplitOrdering.verifySlots_rejecting_suffix
#print axioms AspisR1.OraclePortJoinSplitS2.source_header_total
#print axioms AspisR1.OraclePortJoinSplitS7.residue_total
#print axioms AspisR1.OraclePortJoinSplitS8.row_total
#print axioms AspisR1.OraclePortJoinSplitR17.lookup_join
#print axioms AspisR1.OraclePortJoinSplitR22.total_join_R22

import UnifiedOracleVerifier
import TraceAppend
import R1FollowAppend
import UnifiedOracleTrace
import UnifiedOracleTotalCase
import R1UnifiedOracleInj

/-! Audited checkpoint for terminal oracle-decision trace transport. -/

#print axioms AspisR1.UnifiedOracleVerifier.specializes_done
#print axioms AspisR1.UnifiedOracleVerifier.readsChains
#print axioms AspisR1.UnifiedOracleVerifier.verifier_eval

#print axioms AspisR1.TraceAppend.tableBefore_append
#print axioms AspisR1.TraceAppend.traceFrom_append
#print axioms AspisR1.TraceAppend.firstReads_le_append
#print axioms AspisR1.TraceAppend.hitsBad_of_prefix

#print axioms AspisR1.FollowAppend.follow_append_of_some
#print axioms AspisR1.FollowAppend.bfollow_append_of_some

#print axioms AspisR1.UnifiedOracleTrace.trace_decomposition
#print axioms AspisR1.UnifiedOracleTrace.result_eq_terminal

#print axioms AspisR1.UnifiedOracleTotalCase.decodes_and_follows
#print axioms AspisR1.UnifiedOracleInj.inj

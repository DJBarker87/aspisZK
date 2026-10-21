import OraclePortAccLogSlot
import OraclePortAccLogCones
import OraclePortAccLogHeadline
import OraclePortAccLogCuts

/-! One final compatible focused import audit. This does not replay the full
frozen source/dependency manifest and does not establish the frozen join. -/
#print axioms AspisR1.OraclePortAccLogSlot.accepted_slot_logs_differ
#print axioms AspisR1.OraclePortAccLogSlot.levels_singleton
#print axioms AspisR1.OraclePortAccLog.executionJoin_acceptedRunJoin
#print axioms AspisR1.OraclePortAccLog.acceptedRunJoin_strict
#print axioms AspisR1.OraclePortAccLog.acceptedRunJoin_outer_strict
#print axioms AspisR1.OraclePortAccLog.acceptedRunJoin_of_cones
#print axioms AspisR1.OraclePortAccLog.short_accepted_eq
#print axioms AspisR1.OraclePortAccLog.accepted_recovered_inputs
#print axioms AspisR1.OraclePortAccLog.accepted_extractor_eq
#print axioms AspisR1.OraclePortAccLog.runtime_transport
#print axioms AspisR1.OraclePortHeadlineAccLog.final_soundness
#print axioms AspisR1.OraclePortHeadlineAccLog.per_query
#print axioms AspisR1.OraclePortAccLogParentSchedules.actual_schedule_recovery_obstruction
#print axioms AspisR1.OraclePortAccLogCuts.same_frame_recovery_obstruction

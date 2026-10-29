import PV_L1F_Axioms
/-! Focused accepted closure only; no deployed privacy release claim. -/
#check PV_L1F_Statements.combined
#check PV_L1F_ActualPublication.source_publication_read
#check PV_L1F_LoggedCount.source_logged_count
#check PV_L1F_LoggedCount.source_count_entries
#check PV_L1F_ReachedJoin.reached_producer
#check PV_L1F_ReachedJoin.reached_join
#check PV_L1F_RetryBounds.read_bounds
#check PV_L1F_ReturnedCount.finish_read
#check PV_L1F_ReturnedCount.read_done
#check PV_L1F_ReturnedCount.read_map_state
#check PV_L1F_ReturnedCount.source_read
#check PV_L1F_ReturnedPrefix.counts_suffix
#check PV_L1F_ReturnedPrefix.rejects_suffix
#check PV_L1F_ReturnedPrefix.ordered_acquisition
#check PV_L1F_SourceBounds.actual_count_bounds
#check PV_L1F_SourceRead.actual_retry_count
#check PV_L1F_SourceRead.reported_source_count
#check PV_L1F_WorldFields.runtime_fields
#check PV_L1F_WorldFields.prefix_frame
#check PV_L1F_WorldLog.bind_log
#check PV_L1F_WorldLog.fail_world
#check PV_L1F_WorldLog.div_world
#print axioms PV_L1F_Statements.combined

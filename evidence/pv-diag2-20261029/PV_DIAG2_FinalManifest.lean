import PV_DIAG2_Audit
import PV_DIAG2_ResumeAudit
-- One final manifest of this job's accepted source/model roots, not V397's whole privacy replay.
#check @PV_DIAG2.source_client_no_rejected
#check @PV_DIAG2.client_observed_api_not_rejected
#check @PV_DIAG2.retry_sink_silent
#check @PV_DIAG2.process
#print axioms PV_DIAG2.source_client_no_rejected
#print axioms PV_DIAG2.client_observed_api_not_rejected
#print axioms PV_DIAG2.rejected_not_in_report_suffix
#print axioms PV_DIAG2.cap_requested_text
#print axioms PV_DIAG2.semantic_mapper_exact
#print axioms PV_DIAG2.mask_mapper_exact
#print axioms PV_DIAG2.semantic_mapper_silent
#print axioms PV_DIAG2.mask_mapper_silent
#print axioms PV_DIAG2.termination_success
#print axioms PV_DIAG2.normal_error_exit
#print axioms PV_DIAG2.retry_sink_exact
#print axioms PV_DIAG2.result_equality_not_stderr_equality
#print axioms PV_DIAG2.result_equality_not_frame_equality
#print axioms R1Z.ProverRwRetryModel.retry

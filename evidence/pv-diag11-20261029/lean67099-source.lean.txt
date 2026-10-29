import PV_DIAG11_Audit
import PV_DIAG11_ProducerAudit
import PV_DIAG10_Handoff
/-! One focused local manifest; not the frozen privacy-release manifest.
The three DIAG inputs remain conditional. No new Link definition or instance. -/
#check PV_DIAG10.DIAG_FILE_TRACE
#check PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#check PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG10.DIAG_FILE_TRACE
#print axioms PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#print axioms PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG11.writeAll_same_length_metadata
#print axioms PV_DIAG11.unit_error_operand_link

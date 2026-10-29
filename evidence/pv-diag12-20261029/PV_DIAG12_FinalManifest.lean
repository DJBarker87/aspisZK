import PV_DIAG12_Audit
import PV_DIAG12_ProducerAudit
import PV_DIAG10_Handoff
/- One focused source-layer manifest. No deployed Link instance is asserted.
All three original typed acquisition inputs retain their unchanged links. -/
#check PV_DIAG10.DIAG_FILE_TRACE
#check PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#check PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG10.DIAG_FILE_TRACE
#print axioms PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#print axioms PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG12.jsonStream_append
#print axioms PV_DIAG12.onePrintln_chunks_append
#print axioms PV_DIAG12.pending_prefix_readout

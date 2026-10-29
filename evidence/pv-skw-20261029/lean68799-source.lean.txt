/- Final manifest, statement audit and axioms audit of the compiled model witnesses. -/
import PV_SKW_DIAG_FILE
import PV_SKW_DIAG_JSON_STDOUT
import PV_SKW_DIAG_ERROR_STDERR
import PV_SKW_L1
set_option autoImplicit false
set_option pp.proofs false
#print PV_SKW_DIAG_FILE.Instance
#print PV_SKW_DIAG_FILE.satisfiable
#print PV_SKW_DIAG_FILE.nondegenerate
#print PV_SKW_DIAG_JSON_STDOUT.Instance
#print PV_SKW_DIAG_JSON_STDOUT.satisfiable
#print PV_SKW_DIAG_JSON_STDOUT.nondegenerate
#print PV_SKW_DIAG_ERROR_STDERR.Instance
#print PV_SKW_DIAG_ERROR_STDERR.satisfiable
#print PV_SKW_DIAG_ERROR_STDERR.nondegenerate
#print PV_SKW_L1.Instance
#print PV_SKW_L1.satisfiable
#print PV_SKW_L1.nondegenerate
#print PV_SKW_L1.generic_satisfiable
#print PV_DIAG10.PV_DIAG10_Link_Init
#print PV_DIAG10.PV_DIAG10_Link_Step
#print PV_DIAG10.PV_DIAG10_Link_Readout
#print PV_DIAG10.PV_DIAG10_Link_EventOrder
#print PV_L1E_CountSkeleton.PV_L1E_Link_CountAcquisition
#print PV_L1E_CountSkeleton.PV_L1E_Link_BodyWrapper
#print PV_L1E_CountSkeleton.PV_L1E_Link_RetryJoin
#print PV_L1E_CountSkeleton.PV_L1E_Link_NativeOriginal
#print PV_L1E_OriginalCountSkeleton.PV_L1E_Link_OriginalRetry
#print PV_L1E_OriginalCountSkeleton.PV_L1E_Link_NativeD163

#print axioms PV_SKW_DIAG_FILE.satisfiable
#print axioms PV_SKW_DIAG_FILE.nondegenerate
#print axioms PV_SKW_DIAG_FILE.project_step
#print axioms PV_SKW_DIAG_JSON_STDOUT.satisfiable
#print axioms PV_SKW_DIAG_JSON_STDOUT.nondegenerate
#print axioms PV_SKW_DIAG_JSON_STDOUT.project_step
#print axioms PV_SKW_DIAG_ERROR_STDERR.satisfiable
#print axioms PV_SKW_DIAG_ERROR_STDERR.nondegenerate
#print axioms PV_SKW_DIAG_ERROR_STDERR.project_step
#print axioms PV_SKW_L1.satisfiable
#print axioms PV_SKW_L1.nondegenerate
#print axioms PV_SKW_L1.generic_satisfiable

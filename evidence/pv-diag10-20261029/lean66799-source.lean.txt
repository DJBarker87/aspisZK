import PV_DIAG10_Audit
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
theorem frozen_manifest {I A : Type}
 (files : I → List FileOp) (json : I → List Bytes × List (Bytes × Bytes))
 (errors : I → List PV_DIAG2.Effect × List PV_DIAG3.Event)
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (fr : PV_DIAG10_Link_Readout files sourceFile raw)
 (jr : PV_DIAG10_Link_Readout json sourceJSON raw)
 (er : PV_DIAG10_Link_Readout errors sourceError raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.DIAG_FILE_TRACE files native ∧
 OpenInputs.DIAG_JSON_STDOUT_TRACE json native ∧
 OpenInputs.DIAG_ERROR_STDERR_TRACE errors native :=
 all_three_exact_inputs files json errors native raw fr jr er order
#print axioms frozen_manifest
end PV_DIAG10

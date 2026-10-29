import PV_DIAG10_Links
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
theorem DIAG_JSON_STDOUT_TRACE {I A : Type} (actual : I → List Bytes × List (Bytes × Bytes))
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (state : I → List NativeEvent → List Bytes × List (Bytes × Bytes))
 (initial : PV_DIAG10_Link_Init state ((fun es => (nativeJSON es,nativeStdout es)) []))
 (step : PV_DIAG10_Link_Step state (fun a b => (a.1++b.1,a.2++b.2)) (fun e => (fun es => (nativeJSON es,nativeStdout es)) [e]))
 (readout : PV_DIAG10_Link_Readout actual state raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.DIAG_JSON_STDOUT_TRACE actual native := by
 intro i
 rw [readout i,order i]
 apply prefix_agreement state (fun es => (nativeJSON es,nativeStdout es)) (fun a b => (a.1++b.1,a.2++b.2)) initial step
 intro es e
 simp only [nativeJSON,nativeStdout,List.filterMap_append] <;> rfl
#print axioms DIAG_JSON_STDOUT_TRACE
end PV_DIAG10

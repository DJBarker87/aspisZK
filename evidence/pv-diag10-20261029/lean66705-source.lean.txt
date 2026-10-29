import PV_DIAG10_Links
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
theorem DIAG_ERROR_STDERR_TRACE {I A : Type} (actual : I → List PV_DIAG2.Effect × List PV_DIAG3.Event)
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (state : I → List NativeEvent → List PV_DIAG2.Effect × List PV_DIAG3.Event)
 (initial : PV_DIAG10_Link_Init state ((fun es => (nativeDiag2 es,nativeDiag3 es)) []))
 (step : PV_DIAG10_Link_Step state (fun a b => (a.1++b.1,a.2++b.2)) (fun e => (fun es => (nativeDiag2 es,nativeDiag3 es)) [e]))
 (readout : PV_DIAG10_Link_Readout actual state raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.DIAG_ERROR_STDERR_TRACE actual native := by
 intro i
 rw [readout i,order i]
 apply prefix_agreement state (fun es => (nativeDiag2 es,nativeDiag3 es)) (fun a b => (a.1++b.1,a.2++b.2)) initial step
 intro es e
 simp only [nativeDiag2,nativeDiag3,List.filterMap_append] <;> rfl
#print axioms DIAG_ERROR_STDERR_TRACE
end PV_DIAG10

import PV_DIAG10_Links
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
theorem DIAG_FILE_TRACE {I A : Type} (actual : I → List FileOp)
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (state : I → List NativeEvent → List FileOp)
 (initial : PV_DIAG10_Link_Init state (nativeFiles []))
 (step : PV_DIAG10_Link_Step state List.append (fun e => nativeFiles [e]))
 (readout : PV_DIAG10_Link_Readout actual state raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.DIAG_FILE_TRACE actual native := by
 intro i
 rw [readout i,order i]
 apply prefix_agreement state nativeFiles List.append initial step
 intro es e
 simp only [nativeFiles,List.filterMap_append] <;> rfl
#print axioms DIAG_FILE_TRACE
end PV_DIAG10

import PV_DIAG10_FILE
set_option autoImplicit false
namespace PV_SKW_DIAG_FILE
open PV_RJ4IDB PV_DIAG10
abbrev I := NativeTrace Nat
abbrev X := List FileOp
def project : List NativeEvent → X := nativeFiles
structure Instance where
 actual : I → X
 native : I → NativeTrace Nat
 raw : I → List NativeEvent
 state : I → List NativeEvent → X
/-- Full trace carrier: all bytes, events, finite prefixes and terminal forms. -/
def instance : Instance := ⟨fun i => project i.events,id,NativeTrace.events,fun _ es => project es⟩
theorem project_step (es : List NativeEvent) (e : NativeEvent) :
 project (es++[e]) = List.append (project es) (project [e]) := by
 simp only [project,nativeFiles,nativeJSON,nativeStdout,nativeDiag2,nativeDiag3,List.filterMap_append]
/-- Joint witness; no source-to-native association is asserted. -/
theorem satisfiable : ∃ x : Instance,
 PV_DIAG10_Link_Init x.state (project []) ∧
 PV_DIAG10_Link_Step x.state List.append (fun e => project [e]) ∧
 PV_DIAG10_Link_Readout x.actual x.state x.raw ∧
 PV_DIAG10_Link_EventOrder x.raw x.native := by
 refine ⟨instance,?_,?_,?_,?_⟩
 · intro i; rfl
 · intro i es e; exact project_step es e
 · intro i; rfl
 · intro i; rfl
#print axioms project_step
#print axioms satisfiable
end PV_SKW_DIAG_FILE

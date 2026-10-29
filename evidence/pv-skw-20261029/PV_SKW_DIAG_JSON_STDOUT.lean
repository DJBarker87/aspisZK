import PV_DIAG10_JSON_STDOUT
set_option autoImplicit false
namespace PV_SKW_DIAG_JSON_STDOUT
open PV_RJ4IDB PV_DIAG10
abbrev I := NativeTrace Nat
abbrev X := List Bytes × List (Bytes × Bytes)
def project : List NativeEvent → X := (fun es => (nativeJSON es,nativeStdout es))
structure Instance where
 actual : I → X
 native : I → NativeTrace Nat
 raw : I → List NativeEvent
 state : I → List NativeEvent → X
/-- Full trace carrier: all bytes, events, finite prefixes and terminal forms. -/
def model : Instance := ⟨fun i => project i.events,id,NativeTrace.events,fun _ es => project es⟩
theorem project_step (es : List NativeEvent) (e : NativeEvent) :
 project (es++[e]) = (fun a b => (a.1++b.1,a.2++b.2)) (project es) (project [e]) := by
 simp only [project,nativeFiles,nativeJSON,nativeStdout,nativeDiag2,nativeDiag3,List.filterMap_append] <;> rfl
/-- Joint witness; no source-to-native association is asserted. -/
theorem satisfiable : ∃ x : Instance,
 PV_DIAG10_Link_Init x.state (project []) ∧
 PV_DIAG10_Link_Step x.state (fun a b => (a.1++b.1,a.2++b.2)) (fun e => project [e]) ∧
 PV_DIAG10_Link_Readout x.actual x.state x.raw ∧
 PV_DIAG10_Link_EventOrder x.raw x.native := by
 refine ⟨model,?_,?_,?_,?_⟩
 · intro i; rfl
 · intro i es e; exact project_step es e
 · intro i; rfl
 · intro i; rfl
def sample : I := ⟨[.returned [123,125],.printed [10] [10]],.success 7⟩
theorem nondegenerate : model.actual sample = ([[123,125]],[([10],[10])]) := rfl
#print axioms nondegenerate
#print axioms project_step
#print axioms satisfiable
end PV_SKW_DIAG_JSON_STDOUT

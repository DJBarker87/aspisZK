import PV_EVH_ClientAllocator
import PV_EVH_LiteralDiagnostics
set_option autoImplicit false
namespace PV_EVH_ClientRuntimeFault
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (NativeEvent)

/-- The adopted abort profile runs the installed fixed panic hook, then aborts.
No unwind cleanup is inserted. Native hook installation/selection stays OPEN. -/
def capacityOverflow {A : Type} (writer : PV_EVH_LiteralDiagnostics.Writer)
    (abortEvents : List NativeEvent) : Q A := do
  let _ ← PV_EVH_LiteralDiagnostics.panicHook writer
  PV_EVH_ClientAllocator.abortNull abortEvents

theorem hook_then_abort {A : Type} (writer : PV_EVH_LiteralDiagnostics.Writer)
    (abortEvents : List NativeEvent) (w : State)
    (h : (PV_EVH_LiteralDiagnostics.panicHook writer w).outcome = .returned (.ok ())) :
    capacityOverflow (A := A) writer abortEvents w =
      ⟨.fault (.abort []),(PV_EVH_LiteralDiagnostics.panicHook writer w).state,
        (PV_EVH_LiteralDiagnostics.panicHook writer w).events ++ abortEvents⟩ := by
  simp only [capacityOverflow,Bind.bind,PV_EVH_Runtime.bind,h,PV_EVH_ClientAllocator.abortNull]

theorem hook_fault_prefix {A : Type} (writer : PV_EVH_LiteralDiagnostics.Writer)
    (abortEvents : List NativeEvent) (w : State) (fault : Fault)
    (h : (PV_EVH_LiteralDiagnostics.panicHook writer w).outcome = .fault fault) :
    capacityOverflow (A := A) writer abortEvents w =
      ⟨.fault fault,(PV_EVH_LiteralDiagnostics.panicHook writer w).state,
        (PV_EVH_LiteralDiagnostics.panicHook writer w).events⟩ :=
  bind_fault _ _ _ _ h

#print axioms hook_then_abort
#print axioms hook_fault_prefix
end PV_EVH_ClientRuntimeFault

import PV_EVH_ClientRuntimeFault
set_option autoImplicit false
namespace PV_EVH_ClientOverflow
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (NativeEvent)

/-- The installed-hook/abort model never supplies a source Result view, even
if writing the panic literal itself faults, fails, diverges or exhausts fuel.
Actual hook installation and native writer association remain P. -/
theorem no_source {A : Type} (writer : PV_EVH_LiteralDiagnostics.Writer)
    (abortEvents : List NativeEvent) (w : State) :
    sourceProjection (PV_EVH_ClientRuntimeFault.capacityOverflow
      (A := A) writer abortEvents w).outcome = none := by
  simp only [PV_EVH_ClientRuntimeFault.capacityOverflow,Bind.bind,PV_EVH_Runtime.bind]
  cases h : (PV_EVH_LiteralDiagnostics.panicHook writer w).outcome with
  | fault e => rfl
  | exhausted => rfl
  | returned r =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok u => rfl

#print axioms no_source
end PV_EVH_ClientOverflow

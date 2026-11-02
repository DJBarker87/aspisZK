import PV_EVH_ClientRuntimeFault
set_option autoImplicit false
namespace PV_EVH_ClientOverflow
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (NativeEvent)

/-- Every installed-hook/abort outcome excludes a successful source value.
Source failure/divergence of an unbound Writer are NOT silently reclassified
as native faults. Actual hook/writer association remains P. -/
theorem no_success {A : Type} (writer : PV_EVH_LiteralDiagnostics.Writer)
    (abortEvents : List NativeEvent) (w : State) (a : A) :
    (PV_EVH_ClientRuntimeFault.capacityOverflow
      (A := A) writer abortEvents w).outcome ≠ .returned (.ok a) := by
  simp only [PV_EVH_ClientRuntimeFault.capacityOverflow,Bind.bind,PV_EVH_Runtime.bind]
  cases h : (PV_EVH_LiteralDiagnostics.panicHook writer w).outcome with
  | fault e => intro he; cases he
  | exhausted => intro he; cases he
  | returned r =>
    cases r with
    | fail e => intro he; cases he
    | div => intro he; cases he
    | ok u => intro he; cases he

/-- Why an unconditional PartialView of this unbound hook cannot replace the
old capacity model: source failure has a source projection, unlike a native
fault. It must be ruled out by actual writer fidelity, not a success domain. -/
theorem source_failure_retained {A : Type} (writer : PV_EVH_LiteralDiagnostics.Writer)
    (abortEvents : List NativeEvent) (w : State) (e : Error)
    (h : (PV_EVH_LiteralDiagnostics.panicHook writer w).outcome = .returned (.fail e)) :
    sourceProjection (PV_EVH_ClientRuntimeFault.capacityOverflow
      (A := A) writer abortEvents w).outcome = some (.fail e) := by
  simp only [PV_EVH_ClientRuntimeFault.capacityOverflow,Bind.bind,PV_EVH_Runtime.bind,h,
    sourceProjection]

#print axioms no_success
#print axioms source_failure_retained
end PV_EVH_ClientOverflow

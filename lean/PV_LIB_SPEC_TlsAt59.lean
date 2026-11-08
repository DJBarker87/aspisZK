import PV_LIB_SPEC_Tls277Delivery15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt59
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_Tls59Data15 (token config request wait origin at59)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_TlsAt58 (at58)

theorem context : PV_LIB_SPEC_ResourceHistory.context at58 config wait = some origin := by
  classical
  simp [PV_LIB_SPEC_ResourceHistory.context,at58,PV_LIB_SPEC_Tls277Request15.after,
    PV_LIB_SPEC_Tls59Data15.wait,PV_LIB_SPEC_Tls59Data15.request,
    PV_LIB_SPEC_Tls59Data15.config,PV_LIB_SPEC_Tls59Data15.origin,
    PV_THR2_RunTlsNext.pending,PV_LIB_SPEC_ResourceHistory.arguments,
    PV_LIB_SPEC_Tls59Data15.token,PV_LIB_SPEC_Tls277Native15.token,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl,
    PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_Tls277Request15.site,PV_LIB_SPEC_TlsRequest15.site,PV_THR2_F170.node13,PV_THR2_F170.node16]

theorem consume (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters at58 = at59 := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [PV_LIB_SPEC_Tls59Data15.nonnative]
  rw [context]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment origin
  have result := PV_LIB_SPEC_Tls277Bound15.answer (cut stack) resources config
    PV_LIB_SPEC_Entry14.state 7 PV_LIB_SPEC_Entry13.slot.source wait PV_LIB_SPEC_Tls59Data15.waiting rfl
  change (match PV_LIB_SPEC_ReachedNative14.answer (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config request PV_LIB_SPEC_Entry14.state with
    | none => _ | some _ => _) = at59
  change PV_LIB_SPEC_ReachedNative14.answer (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config request PV_LIB_SPEC_Entry14.state = some ⟨.returned (.ok PV_LIB_SPEC_Tls59Data15.result),PV_LIB_SPEC_Entry14.state,[]⟩ at result
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config at58.state,
      PV_LIB_SPEC_ControlRuntime.recordIssue at58.state
        (PV_LIB_SPEC_ReachedNative14.transition (cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) config at58.state) at58.issued,
      [origin,PV_LIB_SPEC_TlsAt55.origin]⟩ : Execution) = at59
  rw [PV_LIB_SPEC_Tls277Delivery15.transition]
  simp [PV_LIB_SPEC_Tls59Data15.at59,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    at58,PV_LIB_SPEC_Tls277Request15.after,PV_THR2_RunTlsNext.pending]

theorem original59 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 59
      (initial PV_LIB_SPEC_Entry14.input) = at59 := by
  rw [show 59=58+1 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt58.original58]
  exact consume stack

#print axioms context
#print axioms consume
#print axioms original59
end PV_LIB_SPEC_TlsAt59

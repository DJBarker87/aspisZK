import PV_LIB_SPEC_Tls278Delivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt64
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_Tls64Data16 (token config request wait origin at64)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_TlsAt63 (at63)

theorem context : PV_LIB_SPEC_ResourceHistory.context at63 config wait = some origin := by
  rw [PV_LIB_SPEC_ResourceHistory.context,PV_LIB_SPEC_TlsAt63.issued63,
    PV_LIB_SPEC_TlsAt63.consumed63]
  simp [PV_LIB_SPEC_Tls278Values15.token,PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls278Reached15.config,
    PV_LIB_SPEC_Tls278Lift15.config,PV_LIB_SPEC_Tls64Data16.wait,
    PV_LIB_SPEC_Tls278Reached15.wait,PV_LIB_SPEC_Tls278Reached15.request,
    PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls64Data16.request,
    PV_LIB_SPEC_ResourceHistory.arguments,PV_LIB_SPEC_TlsAt55.origin,
    PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_Tls277Request15.site,
    PV_LIB_SPEC_Tls278History15.site,PV_LIB_SPEC_TlsRequest15.site,
    PV_THR2_F170.node13,PV_THR2_F170.node16,PV_THR2_F170.node20,
    show PV_LIB_SPEC_Tls59Data15.store59.nextActivation=8 from rfl]

theorem consume (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters at63 = at64 := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [PV_LIB_SPEC_Tls64Data16.nonnative]
  rw [context]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment origin
  have result := PV_LIB_SPEC_Tls278Bound15.answer (cut stack) resources config
    PV_LIB_SPEC_Entry14.state 8 PV_LIB_SPEC_Entry13.slot.source wait PV_LIB_SPEC_Tls64Data16.waiting rfl
  change (match PV_LIB_SPEC_ReachedNative14.answer (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config request PV_LIB_SPEC_Entry14.state with
    | none => _ | some _ => _) = at64
  change PV_LIB_SPEC_ReachedNative14.answer (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config request PV_LIB_SPEC_Entry14.state = some ⟨.returned (.ok PV_LIB_SPEC_Tls64Data16.result),PV_LIB_SPEC_Entry14.state,[]⟩ at result
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config at63.state,
      PV_LIB_SPEC_ControlRuntime.recordIssue at63.state
        (PV_LIB_SPEC_ReachedNative14.transition (cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) config at63.state) at63.issued,
      origin :: at63.consumed⟩ : Execution) = at64
  rw [PV_LIB_SPEC_Tls278Delivery16.transition]
  simp only [PV_LIB_SPEC_Tls64Data16.at64]
  rw [PV_LIB_SPEC_TlsAt63.state63]
  rfl

theorem original64 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 64
      (initial PV_LIB_SPEC_Entry14.input) = at64 := by
  rw [show 64=63+1 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt63.original63]
  exact consume stack

#print axioms context
#print axioms consume
#print axioms original64
end PV_LIB_SPEC_TlsAt64

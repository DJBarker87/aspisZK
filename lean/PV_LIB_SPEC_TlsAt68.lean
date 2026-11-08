import PV_LIB_SPEC_Tls279Delivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt68
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_Tls68Data16 (token config request wait origin at68)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_TlsAt67 (at67)

theorem context : PV_LIB_SPEC_ResourceHistory.context at67 config wait = some origin := by
  rw [PV_LIB_SPEC_ResourceHistory.context,PV_LIB_SPEC_TlsAt67.issued67,
    PV_LIB_SPEC_TlsAt67.consumed67]
  simp [PV_LIB_SPEC_Tls68Data16.token,PV_LIB_SPEC_Tls279Values16.token,PV_LIB_SPEC_Tls68Data16.config,
    PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_LIB_SPEC_Tls68Data16.wait,PV_LIB_SPEC_Tls68Data16.request,
    PV_LIB_SPEC_Tls68Data16.origin,PV_LIB_SPEC_ResourceHistory.arguments,
    PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,
    PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_Tls279History16.site,
    PV_LIB_SPEC_Tls278History15.site,PV_LIB_SPEC_Tls277Request15.site,
    PV_LIB_SPEC_TlsRequest15.site,PV_THR2_F170.node13,PV_THR2_F170.node16,
    PV_THR2_F170.node20,PV_THR2_F170.node23,
    show PV_LIB_SPEC_Tls64Data16.store64.nextActivation=9 from rfl]

theorem consume (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters at67 = at68 := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [PV_LIB_SPEC_Tls68Data16.nonnative]
  rw [context]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment origin
  have result := PV_LIB_SPEC_Tls279Bound16.answer (cut stack) resources config
    PV_LIB_SPEC_Entry14.state 9 PV_LIB_SPEC_Entry13.slot.source wait PV_LIB_SPEC_Tls68Data16.waiting rfl
  change (match PV_LIB_SPEC_ReachedNative14.answer (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config request PV_LIB_SPEC_Entry14.state with
    | none => _ | some _ => _) = at68
  change PV_LIB_SPEC_ReachedNative14.answer (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config request PV_LIB_SPEC_Entry14.state = some ⟨.returned (.ok PV_LIB_SPEC_Tls68Data16.result),PV_LIB_SPEC_Entry14.state,[]⟩ at result
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config at67.state,
      PV_LIB_SPEC_ControlRuntime.recordIssue at67.state
        (PV_LIB_SPEC_ReachedNative14.transition (cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) config at67.state) at67.issued,
      origin :: at67.consumed⟩ : Execution) = at68
  rw [PV_LIB_SPEC_Tls279Delivery16.transition]
  simp only [PV_LIB_SPEC_Tls68Data16.at68]
  rw [PV_LIB_SPEC_TlsAt67.state67]
  rfl

theorem original68 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 68
      (initial PV_LIB_SPEC_Entry14.input) = at68 := by
  rw [show 68=67+1 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt67.original67]
  exact consume stack

#print axioms context
#print axioms consume
#print axioms original68
end PV_LIB_SPEC_TlsAt68

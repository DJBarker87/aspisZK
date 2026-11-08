import PV_LIB_SPEC_Tls18Delivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt85
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_TlsAt84 (config at84)
open PV_LIB_SPEC_Tls85Data16 (wait origin at85)
open PV_LIB_SPEC_Tls18Bound16 (request)
open PV_LIB_SPEC_TlsNative15 (cut)

theorem context : PV_LIB_SPEC_ResourceHistory.context at84 config wait = some origin := by
  rw [PV_LIB_SPEC_ResourceHistory.context,PV_LIB_SPEC_TlsAt84.issued84,
    PV_LIB_SPEC_TlsAt84.consumed84,PV_LIB_SPEC_TlsAt75.consumed75]
  change _ = some origin
  simp [config,PV_LIB_SPEC_TlsCallable16.config,wait,origin,request,
    PV_LIB_SPEC_Tls18Bound16.arguments,PV_LIB_SPEC_Tls18Bound16.token,
    PV_LIB_SPEC_ResourceHistory.arguments,PV_LIB_SPEC_Tls68Data16.at68,
    PV_LIB_SPEC_TlsAt67.consumed67,PV_LIB_SPEC_Tls68Data16.origin,
    PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,
    PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_TlsCallableHistory16.site,
    PV_LIB_SPEC_Tls279History16.site,PV_LIB_SPEC_Tls278History15.site,
    PV_LIB_SPEC_Tls277Request15.site,PV_LIB_SPEC_TlsRequest15.site,
    PV_THR2_F170.node13,PV_THR2_F170.node16,PV_THR2_F170.node20,
    PV_THR2_F170.node23,PV_THR2_F170.node55,
    show PV_LIB_SPEC_TlsAt75.store75.nextActivation=10 from rfl]

theorem consume (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters at84 = at85 := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [PV_LIB_SPEC_Tls85Data16.ordinary]
  rw [context]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment origin
  have result := PV_LIB_SPEC_Tls18Bound16.answer stack resources config
    PV_LIB_SPEC_Entry14.state 10 (PV_LIB_SPEC_Tls18Reached16.active resources)
  change (match PV_LIB_SPEC_ReachedNative14.answer (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config (request 10) PV_LIB_SPEC_Entry14.state with
    | none => _ | some _ => _) = at85
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config at84.state,
      PV_LIB_SPEC_ControlRuntime.recordIssue at84.state
        (PV_LIB_SPEC_ReachedNative14.transition (cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) config at84.state) at84.issued,
      origin :: at84.consumed⟩ : Execution) = at85
  rw [PV_LIB_SPEC_Tls18Delivery16.transition]
  simp only [PV_LIB_SPEC_Tls85Data16.at85]
  rw [PV_LIB_SPEC_TlsAt84.state84]
  rfl

theorem original85 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 85
      (initial PV_LIB_SPEC_Entry14.input) = at85 := by
  rw [show 85=84+1 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt84.original84]
  exact consume stack

#print axioms context
#print axioms consume
#print axioms original85
end PV_LIB_SPEC_TlsAt85

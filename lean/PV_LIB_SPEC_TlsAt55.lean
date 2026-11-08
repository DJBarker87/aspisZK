import PV_LIB_SPEC_TlsDelivery15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt55
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_TlsAt54 (token initValue config at54)
open PV_LIB_SPEC_TlsNative15 (cut request reference)

def wait : PV_STX2_Native.Waiting Data := ⟨request,.child 6 (.local 7),[]⟩
def origin : Context := ⟨PV_LIB_SPEC_TlsRequest15.site,0,[initValue],5,request⟩
def at55 : Execution := ⟨PV_LIB_SPEC_TlsDelivery15.after,at54.issued,[origin]⟩

theorem ordinary : PV_LIB_SPEC_ControlRuntime.ordinary at54.state = some (config,wait) := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,at54,PV_LIB_SPEC_TlsRequest15.after,
    PV_THR2_Catch316Segment.select,lookup,wait,request,config,
    show PV_LIB_SPEC_TlsAt54.store53.nextActivation=6 from rfl]

theorem context : PV_LIB_SPEC_ResourceHistory.context at54 config wait = some origin := by
  classical
  simp [PV_LIB_SPEC_ResourceHistory.context,at54,PV_LIB_SPEC_TlsRequest15.after,
    wait,request,config,origin,PV_LIB_SPEC_ResourceHistory.arguments,
    show PV_LIB_SPEC_TlsAt54.store53.nextActivation=6 from rfl]

theorem consume (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters at54 = at55 := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [ordinary]
  rw [context]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment origin
  have result := PV_LIB_SPEC_TlsBound15.answer stack resources
  change (match PV_LIB_SPEC_ReachedNative14.answer (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config request PV_LIB_SPEC_Entry14.state with
    | none => _ | some _ => _) = at55
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) config at54.state,
      PV_LIB_SPEC_ControlRuntime.recordIssue at54.state
        (PV_LIB_SPEC_ReachedNative14.transition (cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) config at54.state) at54.issued,
      [origin]⟩ : Execution) = at55
  rw [PV_LIB_SPEC_TlsDelivery15.transition]
  simp [at55,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    at54,PV_LIB_SPEC_TlsRequest15.after]

theorem original55 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 55
      (initial PV_LIB_SPEC_Entry14.input) = at55 := by
  rw [show 55=54+1 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt54.original54]
  exact consume stack

#print axioms wait
#print axioms origin
#print axioms at55
#print axioms ordinary
#print axioms context
#print axioms consume
#print axioms original55
end PV_LIB_SPEC_TlsAt55

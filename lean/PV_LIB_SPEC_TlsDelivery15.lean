import PV_LIB_SPEC_TlsBound15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsDelivery15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsAt54 (token initValue config)
open PV_LIB_SPEC_TlsNative15 (cut request reference)

def store55 : Store Data := write (write config.store ⟨6,0,[]⟩ (some reference)) ⟨5,7,[]⟩ (some reference)
def after : State :=
  (stage store55 5 PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 14)
    PV_LIB_SPEC_Entry14.state [] [] []).state

theorem transition (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      config PV_LIB_SPEC_TlsAt54.at54.state = after := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  have table : PV_LIB_StoreActionTable.v2 token = none := rfl
  have returned := PV_LIB_SPEC_TlsBound15.answer stack resources
  simp [request,config,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node14] at returned
  change PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config ⟨⟨.running config,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ = after
  simp [stage,after,store55,config,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    
    PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node14,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    lookup,table,PV_LIB_SPEC_ReachedNative14.handler,returned,
    PV_STX2_Native.reply,PV_STX2_Native.storeResult,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply]
#print axioms store55
#print axioms after
#print axioms transition
end PV_LIB_SPEC_TlsDelivery15

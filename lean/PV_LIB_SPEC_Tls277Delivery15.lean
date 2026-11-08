import PV_LIB_SPEC_Tls59Data15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls277Delivery15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_Tls59Data15
open PV_LIB_SPEC_TlsNative15 (cut reference)

theorem transition (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      config PV_LIB_SPEC_TlsAt58.at58.state = after := by
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunTlsNext.callee = none := rfl
  have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsNext.callee = none := rfl
  have returned := PV_LIB_SPEC_Tls277Bound15.answer (cut stack) resources config
    PV_LIB_SPEC_Entry14.state 7 PV_LIB_SPEC_Entry13.slot.source wait waiting rfl
  simp [config,PV_THR2_RunTlsNext.pending,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node17,
    PV_LIB_SPEC_Tls277Native15.token,PV_LIB_SPEC_Tls277Native15.pointer,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl,
    ← show reference=PV_STX2_TypedReferences.reference PV_LIB_SPEC_Entry13.slot.source .null from rfl] at returned
  change PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config ⟨⟨.running config,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ = after
  simp [stage,after,store59,config,PV_THR2_RunTlsNext.pending,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    
    PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node17,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    lookup,table,PV_LIB_SPEC_ReachedNative14.handler,returned,token,PV_LIB_SPEC_Tls277Native15.token,
    result,PV_LIB_SPEC_Tls277Native15.value,show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl,
    PV_STX2_Native.reply,PV_STX2_Native.storeResult,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply]
#print axioms transition
end PV_LIB_SPEC_Tls277Delivery15

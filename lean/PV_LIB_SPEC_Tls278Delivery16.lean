import PV_LIB_SPEC_NativeDelivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls278Delivery16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls64Data16
open PV_LIB_SPEC_TlsNative15 (cut)

theorem transition (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      config PV_LIB_SPEC_TlsAt63.at63.state = after := by
  rw [PV_LIB_SPEC_TlsAt63.state63]
  change PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config ⟨⟨.running config,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ = after
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet
      ⟨⟨.running config,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ := by
    have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunTlsErrorCompleted.callee = none := rfl
    have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsErrorCompleted.callee = none := rfl
    simp [lookup,table,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node21,
      PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,config,PV_LIB_SPEC_Tls278Reached15.config,
      PV_LIB_SPEC_Tls278Lift15.config,PV_THR2_OwnInitAction.selected,
      PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction]
  rw [PV_LIB_SPEC_NativeDelivery16.full (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config PV_LIB_SPEC_Entry14.state [] [] wait token 8 5
    [PV_LIB_SPEC_Tls59Data15.result,PV_LIB_SPEC_Tls278Lift15.error]
    quiet (by rfl) rfl rfl waiting rfl (by rfl)]
  have reply := PV_LIB_SPEC_Tls278Bound15.answer (cut stack) resources config
    PV_LIB_SPEC_Entry14.state 8 PV_LIB_SPEC_Entry13.slot.source wait waiting rfl
  change PV_LIB_SPEC_ReachedNative14.answer (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config request PV_LIB_SPEC_Entry14.state = some ⟨.returned (.ok result),PV_LIB_SPEC_Entry14.state,[]⟩ at reply
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show wait.request=request from rfl,reply,Option.getD_some]
  rfl

#print axioms transition
end PV_LIB_SPEC_Tls278Delivery16

import PV_LIB_SPEC_Tls85Data16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls18Delivery16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls85Data16
open PV_LIB_SPEC_TlsAt84 (config at84)
open PV_LIB_SPEC_Tls18Bound16 (token arguments request)
open PV_LIB_SPEC_TlsNative15 (cut)

theorem lookup : PV_LIB_SPEC_Full.programs token = none := by
  have ne : token ≠ PV_THR2_Catch208Invoke.fn := by
    intro eq
    have same := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases same
  change PV_THR2_Source208Table.table _ token = none
  rw [PV_THR2_Source208Table.away _ _ ne]
  rfl

theorem transition (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      config at84.state = after := by
  rw [PV_LIB_SPEC_TlsAt84.state84]
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet
      ⟨⟨.running config,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ := by
    have table : PV_LIB_StoreActionTable.v2 token = none := rfl
    simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,config,PV_LIB_SPEC_TlsCallable16.config,
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
      PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
      PV_THR2_OwnUniformNeutral.instruction,PV_THR2_F170.live,PV_THR2_F170.block66,
      PV_THR2_F170.node56,← show token=PV_THR2_RunTlsCallable.descriptors.1 from rfl,
      lookup,table]
  rw [PV_LIB_SPEC_NativeDelivery16.full (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    config PV_LIB_SPEC_Entry14.state [] [] wait token 10 14 arguments
    quiet (by rfl) rfl rfl waiting rfl lookup]
  have reply := PV_LIB_SPEC_Tls18Bound16.answer stack resources config
    PV_LIB_SPEC_Entry14.state 10 (PV_LIB_SPEC_Tls18Reached16.active resources)
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show wait.request=request 10 from rfl,
    reply,Option.getD_some]
  rfl

#print axioms lookup
#print axioms transition
end PV_LIB_SPEC_Tls18Delivery16

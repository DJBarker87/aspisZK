import PV_LIB_SPEC_Tls278Route15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls278Native15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls278Values15 (token value pure)

theorem native (regs : PV_LIB_SPEC_CallbackStores.Registers) (p : Parameters)
    (c : Config) (w : OWNER) (a : Nat) (address : Address)
    (trigger : PV_THR2_OwnUniformResourceHandler.lift p.environment.native
      (.child token a [PV_LIB_SPEC_Tls277Native15.value address,PV_LIB_SPEC_Tls278Lift15.error]) w =
        ⟨.returned (.ok .null),w,[]⟩) :
    PV_LIB_SPEC_CallbackRuntime.native regs p c
      (.child token a [PV_LIB_SPEC_Tls277Native15.value address,PV_LIB_SPEC_Tls278Lift15.error]) w =
      some ⟨.returned (.ok (value address)),w,[]⟩ := by
  unfold PV_LIB_SPEC_CallbackRuntime.native
  dsimp only
  simp only [PV_LIB_SPEC_SiteArc.handler,PV_LIB_SPEC_CallbackStores.handler,
    PV_THR2_PacketPointerSemantics.handler,PV_THR2_IntrinsicSemantics_NonNullFrom217.handler,
    PV_THR2_IntrinsicSemantics_BoxIntoRawWithAllocator312.handler,
    PV_THR2_IntrinsicSemantics_MemForget313.handler,
    PV_THR2_IntrinsicSemantics_NonNullAsRef.handler,PV_THR2_ManuallyDropHandler.handler,
    PV_THR2_IntrinsicSemantics_ManuallyDropNew134.handler,
    PV_THR2_IntrinsicSemantics_ManuallyDropDerefMut344.handler,
    PV_THR2_FnOnceDispatch.handler,PV_THR2_FnOnceDispatch.request,
    show PV_THR2_FnOnceDispatch.isFnOnce token=false from rfl,
    Bool.false_and,Bool.false_eq_true,ite_false,
    PV_LIB_SPEC_SparseRuntime.values,show PV_THR2_OffPath.functionId token=some 278 from rfl,
    trigger,pure]
  rfl

#print axioms native
end PV_LIB_SPEC_Tls278Native15

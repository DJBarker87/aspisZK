import PV_LIB_SPEC_Tls279Route16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls279Native16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls279Values16 (token value pure)

theorem different (other : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId other = some id) (ne : 279≠id) : token ≠ other := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 279 = PV_THR2_OffPath.functionId other at same
  rw [number] at same
  exact ne (Option.some.inj same)

theorem native (regs : PV_LIB_SPEC_CallbackStores.Registers) (p : Parameters)
    (c : Config) (w : OWNER) (a : Nat) (address : Address)
    (trigger : PV_THR2_OwnUniformResourceHandler.lift p.environment.native
      (.child token a [PV_LIB_SPEC_Tls278Values15.value address]) w =
        ⟨.returned (.ok .null),w,[]⟩) :
    PV_LIB_SPEC_CallbackRuntime.native regs p c
      (.child token a [PV_LIB_SPEC_Tls278Values15.value address]) w =
      some ⟨.returned (.ok (value address)),w,[]⟩ := by
  classical
  have nBox : token ≠ PV_THR2_Source361BoxTable.fnClosureBoxFull := by
    intro h; have bad := congrArg PV_THR2_OffPath.functionId h; cases bad
  have n217 : token ≠ PV_THR2_Packet124ReturnData.intoFn := different _ 217 rfl (by decide)
  have n312 : token ≠ PV_THR2_Packet216Children.fn5 := different _ 312 rfl (by decide)
  have n313 : token ≠ PV_THR2_Packet216Children.fn15 := different _ 313 rfl (by decide)
  have n320 : token ≠ PV_THR2_PacketInner320.fn := different _ 320 rfl (by decide)
  have n134 : token ≠ PV_THR2_Source361BoxTable.fn443NewFull := different _ 134 rfl (by decide)
  have n344 : token ≠ PV_THR2_Source361BoxTable.fn443DerefFull := different _ 344 rfl (by decide)
  unfold PV_LIB_SPEC_CallbackRuntime.native
  dsimp only
  have arcAway (H : Handler) (s : Store Data) : PV_LIB_SPEC_SiteArc.handler
      (runtime p).carrier (runtime p).control p.resources p.encode s H
      (.child token a [PV_LIB_SPEC_Tls278Values15.value address]) w = some (H (.child token a [PV_LIB_SPEC_Tls278Values15.value address]) w) := rfl
  rw [arcAway]
  simp only [PV_LIB_SPEC_CallbackStores.handler,if_neg nBox]
  rw [PV_THR2_PacketPointerSemantics.away _ _ _ _ _ n217 n312 n313,
    PV_THR2_IntrinsicSemantics_NonNullAsRef.away _ _ _ _ _ _ _ n320]
  unfold PV_THR2_ManuallyDropHandler.handler
  rw [PV_THR2_IntrinsicSemantics_ManuallyDropNew134.away _ _ _ _ _ n134,
    PV_THR2_IntrinsicSemantics_ManuallyDropDerefMut344.away _ _ _ _ _ n344]
  simp only [PV_THR2_FnOnceDispatch.handler,PV_THR2_FnOnceDispatch.request,
    PV_LIB_SPEC_SparseRuntime.values,show PV_THR2_OffPath.functionId token=some 279 from rfl,
    trigger,pure]

#print axioms different
#print axioms native
end PV_LIB_SPEC_Tls279Native16

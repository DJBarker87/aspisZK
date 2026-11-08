import PV_LIB_SPEC_Tls277Route15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls277Native15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

def token : Data := PV_THR2_RunTlsNext.callee
def pointer (address : Address) : Data := PV_STX2_TypedReferences.reference address .null
def value (address : Address) : Data :=
  (PV_FN_THREAD_f170.SourceTlsValue.optionSome PV_LIB_SPEC_FrozenABI.optionType address).encode

theorem different (other : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId other = some id) (ne : 277≠id) : token ≠ other := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 277 = PV_THR2_OffPath.functionId other at same
  rw [number] at same
  exact ne (Option.some.inj same)

theorem pure (p : Parameters) (w : OWNER) (address : Address) :
    PV_LIB_SPEC_SparseRuntime.pureValue (runtime p).carrier (runtime p).control w
      token [pointer address] = some (value address) := by
  have deref : (runtime p).carrier.dereference w (pointer address) = some address := by
    simp only [pointer,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
      PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
      PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]
  unfold PV_LIB_SPEC_SparseRuntime.pureValue
  rw [show PV_THR2_OffPath.functionId token=some 277 from rfl]
  simp only [deref,Option.some.injEq]
  rfl

theorem native (regs : PV_LIB_SPEC_CallbackStores.Registers) (p : Parameters)
    (c : Config) (w : OWNER) (a : Nat) (address : Address)
    (trigger : PV_THR2_OwnUniformResourceHandler.lift p.environment.native
      (.child token a [pointer address]) w = ⟨.returned (.ok .null),w,[]⟩) :
    PV_LIB_SPEC_CallbackRuntime.native regs p c (.child token a [pointer address]) w =
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
      (.child token a [pointer address]) w = some (H (.child token a [pointer address]) w) := rfl
  rw [arcAway]
  simp only [PV_LIB_SPEC_CallbackStores.handler,if_neg nBox]
  rw [PV_THR2_PacketPointerSemantics.away _ _ _ _ _ n217 n312 n313,
    PV_THR2_IntrinsicSemantics_NonNullAsRef.away _ _ _ _ _ _ _ n320]
  unfold PV_THR2_ManuallyDropHandler.handler
  rw [PV_THR2_IntrinsicSemantics_ManuallyDropNew134.away _ _ _ _ _ n134,
    PV_THR2_IntrinsicSemantics_ManuallyDropDerefMut344.away _ _ _ _ _ n344]
  simp only [PV_THR2_FnOnceDispatch.handler,PV_THR2_FnOnceDispatch.request,
    PV_LIB_SPEC_SparseRuntime.values,show PV_THR2_OffPath.functionId token=some 277 from rfl,
    trigger,pure]

#print axioms token
#print axioms pointer
#print axioms value
#print axioms different
#print axioms pure
#print axioms native
end PV_LIB_SPEC_Tls277Native15

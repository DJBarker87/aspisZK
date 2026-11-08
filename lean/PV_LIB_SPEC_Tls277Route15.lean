import PV_LIB_SPEC_TlsAt58
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls277Route15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

theorem route (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (w : OWNER) (a : Nat) (fn arg value : Data) (events : List Event)
    (id : PV_THR2_OffPath.functionId fn = some 277)
    (lower : PV_LIB_SPEC_CallbackRuntime.answer ⟨cut.native.memory.stack.rsp,0,0,0⟩ p c
      (.child fn a [arg]) w = some ⟨.returned (.ok value),w,events⟩) :
    PV_LIB_SPEC_ReachedNative14.answer cut p c (.child fn a [arg]) w =
      some ⟨.returned (.ok value),w,events⟩ := by
  classical
  have n268 : fn ≠ PV_LIB_SPEC_RawVec14.token := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n164 : fn ≠ PV_LIB_SPEC_PreludeValues14.fn164 := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n165 : fn ≠ PV_LIB_SPEC_PreludeValues14.fn165 := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n93 : fn ≠ PV_LIB_SPEC_PreludeValues14.fn93 := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n295 : fn ≠ PV_LIB_SPEC_StackSize14.token := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n453 : fn ≠ PV_THR2_Source361HookChildren.fnTrueFull := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n454 : fn ≠ PV_THR2_Source361HookChildren.fnFalseFull := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n469 : fn ≠ (PV_THR2_KeyValues.castToken false).2 := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have n18 : fn ≠ PV_THR2_F2Call.descriptors.2 := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have nArc : fn ≠ PV_THR2_Packet124BoxIssue17.fn := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have nBox : fn ≠ PV_THR2_Source361BoxTable.fnClosureBoxFull := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id] at bad
    cases bad
  have tls : PV_LIB_SPEC_TlsBindings13.selected (.child fn a [arg]) = false := by
    simp [PV_LIB_SPEC_TlsBindings13.selected,PV_THR2_FnOnceDispatch.request,n469,n18]
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    if_neg n268,PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    if_neg n164,if_neg n165,if_neg n93,PV_LIB_SPEC_PrefixNative14.answer,
    PV_LIB_SPEC_PrefixNative14.core,if_neg n295,if_neg n454,if_neg n453,
    PV_LIB_SPEC_PrefixNative13.answer,PV_LIB_SPEC_PrefixNative13.core,id,
    show ¬(some 277 = (some 269 : Option Nat)) from by decide,ite_false,
    PV_LIB_SPEC_BoundNative13.answer,PV_LIB_SPEC_BoundNative13.core,
    PV_LIB_SPEC_Native13.answer,PV_LIB_SPEC_Native13.core,tls,Bool.false_eq_true,ite_false,
    PV_LIB_SPEC_NativeMemory12.answer,PV_LIB_SPEC_NativeMemory12.core,id,
    show ¬(some 277 = (some 122 : Option Nat)) from by decide,
    show ¬(some 277 = (some 214 : Option Nat)) from by decide,ite_false,
    PV_LIB_SPEC_SourceNative12.answer,PV_LIB_SPEC_SourceNative12.core,
    PV_LIB_SPEC_CallbackModel.isCallback,nBox,decide_false,Bool.false_eq_true,ite_false,
    PV_LIB_SPEC_NativeBindings12.answer,PV_LIB_SPEC_NativeBindings12.core,
    PV_LIB_SPEC_NativeBindings12.isArc,nArc,decide_false,Bool.false_eq_true,ite_false,
    PV_LIB_SPEC_NativeConstructors.selected,id,
    show ¬(some 277 = (some 213 : Option Nat)) from by decide,ite_false,
    PV_LIB_SPEC_NativeModel.answer,PV_LIB_SPEC_NativeModel.isArc,nArc,decide_false,Bool.false_eq_true,ite_false,
    PV_LIB_SPEC_CallbackModel.answer,PV_LIB_SPEC_CallbackModel.isCallback,nBox,decide_false,Bool.false_eq_true,ite_false,
    lower]
  cases marked : PV_LIB_SPEC_BoundRuntime.allocationToken (.child fn a [arg]) <;>
    simp only [Option.map_some,PV_LIB_SPEC_BoundRuntime.frameReply,marked,
      Bool.false_eq_true,ite_false,ite_true] <;> rfl

#print axioms route
end PV_LIB_SPEC_Tls277Route15

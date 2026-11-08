import PV_LIB_A_F5ClosurePending16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5CallbackObstruction16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_A_F5ClosurePending16 (request)

theorem not_arc : PV_THR2_RunTlsCallable.descriptors.1 ≠ PV_THR2_Packet124BoxIssue17.fn := by
  intro eq
  have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
  change (some (38964,0) : Option (Nat × Nat)) = none at bad
  cases bad

theorem answer_pending (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (s : Store Data) (a : Nat) (parents : List Frame) (pointer : Address) (w : OWNER) :
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources)
      (PV_LIB_SPEC_TlsCallable16.config s a parents PV_LIB_A_F5FullEntry16.closure pointer)
      (request s.nextActivation pointer) w = some ⟨.pending,w,[]⟩ := by
  classical
  have n268 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_RawVec14.token 268 rfl
  have n164 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl
  have n165 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl
  have n93 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl
  have n295 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_StackSize14.token 295 rfl
  have n453 := PV_LIB_SPEC_Tls18Bound16.different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl
  have n454 := PV_LIB_SPEC_Tls18Bound16.different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl
  dsimp only [PV_LIB_SPEC_Tls18Bound16.token] at n268 n164 n165 n93 n295 n453 n454
  have raw := PV_LIB_A_F5ClosurePending16.backend_pending resources w s.nextActivation pointer
  have unselected := PV_LIB_A_F5ClosurePending16.unselected s.nextActivation pointer
  have forwarded := PV_LIB_A_F5ClosurePending16.unforwarded s.nextActivation pointer
  simp only [request] at raw unselected forwarded
  have id : PV_THR2_OffPath.functionId PV_THR2_RunTlsCallable.descriptors.1 = none := rfl
  simp [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    PV_LIB_SPEC_PrefixNative14.answer,PV_LIB_SPEC_PrefixNative14.core,
    PV_LIB_SPEC_PrefixNative13.answer,PV_LIB_SPEC_PrefixNative13.core,
    PV_LIB_SPEC_BoundNative13.answer,PV_LIB_SPEC_BoundNative13.core,
    PV_LIB_SPEC_Native13.answer,PV_LIB_SPEC_Native13.core,
    PV_LIB_SPEC_NativeMemory12.answer,PV_LIB_SPEC_NativeMemory12.core,
    PV_LIB_SPEC_SourceNative12.answer,PV_LIB_SPEC_SourceNative12.core,
    PV_LIB_SPEC_NativeBindings12.answer,PV_LIB_SPEC_NativeBindings12.core,PV_LIB_SPEC_NativeBindings12.isArc,
    PV_LIB_SPEC_NativeConstructors.selected,PV_LIB_SPEC_NativeModel.answer,PV_LIB_SPEC_NativeModel.isArc,
    PV_LIB_SPEC_CallbackModel.answer,PV_LIB_SPEC_CallbackModel.isCallback,
    PV_LIB_SPEC_CallbackRuntime.answer,PV_LIB_SPEC_CallbackRuntime.valueAnswer,
    PV_LIB_SPEC_CallbackRuntime.invalidPure,PV_LIB_SPEC_CallbackRuntime.native,
    PV_LIB_SPEC_SiteArc.handler,PV_LIB_SPEC_CallbackStores.handler,
    PV_THR2_PacketPointerSemantics.handler,PV_THR2_ManuallyDropHandler.handler,
    PV_THR2_IntrinsicSemantics_NonNullFrom217.handler,
    PV_THR2_IntrinsicSemantics_BoxIntoRawWithAllocator312.handler,
    PV_THR2_IntrinsicSemantics_MemForget313.handler,
    PV_THR2_IntrinsicSemantics_NonNullAsRef.handler,
    PV_THR2_IntrinsicSemantics_ManuallyDropNew134.handler,
    PV_THR2_IntrinsicSemantics_ManuallyDropDerefMut344.handler,
    PV_THR2_FnOnceDispatch.handler,PV_LIB_SPEC_SparseRuntime.values,
    PV_LIB_SPEC_BoundRuntime.frameReply,PV_LIB_SPEC_BoundRuntime.allocationToken,
    PV_LIB_SPEC_TlsCallable16.config,request,n268,n164,n165,n93,n295,n453,n454,
    not_arc,id,unselected,forwarded,raw]

#print axioms not_arc
#print axioms answer_pending
end PV_LIB_A_F5CallbackObstruction16

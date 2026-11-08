import PV_LIB_A_F5FullEntry16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F5ClosurePending16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

def request (a : Nat) (p : Address) : PV_STX2_Native.Request Data :=
  .child PV_THR2_RunTlsCallable.descriptors.1 a [PV_LIB_A_F5FullEntry16.closure,
    PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
      [PV_STX2_TypedReferences.reference p .null]]

theorem unforwarded (a : Nat) (p : Address) :
    PV_THR2_FnOnceDispatch.request (request a p) = request a p := rfl

theorem unselected (a : Nat) (p : Address) :
    PV_LIB_SPEC_TlsBindings13.selected (request a p) = false := by
  classical
  have n469 := PV_LIB_SPEC_Tls18Bound16.different (PV_THR2_KeyValues.castToken false).2 469 rfl
  have n18 := PV_LIB_SPEC_Tls18Bound16.different PV_THR2_F2Call.descriptors.2 18 rfl
  unfold PV_LIB_SPEC_TlsBindings13.selected
  rw [unforwarded]
  change decide (PV_LIB_SPEC_Tls18Bound16.token = (PV_THR2_KeyValues.castToken false).2 ∨
    PV_LIB_SPEC_Tls18Bound16.token = PV_THR2_F2Call.descriptors.2) = false
  simp only [n469,n18,false_or,decide_false]

theorem backend_pending (resources : Resources) (w : OWNER) (a : Nat) (p : Address) :
    PV_THR2_OwnUniformResourceHandler.lift (PV_LIB_SPEC_TlsBound15.parameters resources).environment.native
      (request a p) w = ⟨.pending,w,[]⟩ := by
  classical
  have n268 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_RawVec14.token 268 rfl
  have n164 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl
  have n165 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl
  have n93 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl
  have n295 := PV_LIB_SPEC_Tls18Bound16.different PV_LIB_SPEC_StackSize14.token 295 rfl
  have n453 := PV_LIB_SPEC_Tls18Bound16.different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl
  have n454 := PV_LIB_SPEC_Tls18Bound16.different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl
  dsimp only [PV_LIB_SPEC_Tls18Bound16.token] at n268 n164 n165 n93 n295 n453 n454
  have unselected := unselected a p
  simp only [request] at unselected
  simp only [PV_THR2_OwnUniformResourceHandler.lift,PV_LIB_SPEC_TlsBound15.parameters,
    PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
    PV_LIB_SPEC_ReachedEnvironment14.native,request,
    if_neg (show ¬(PV_THR2_RunTlsCallable.descriptors.1=PV_LIB_SPEC_RawVec14.token ∨
      PV_THR2_RunTlsCallable.descriptors.1=PV_LIB_SPEC_PreludeValues14.fn164 ∨
      PV_THR2_RunTlsCallable.descriptors.1=PV_LIB_SPEC_PreludeValues14.fn165 ∨
      PV_THR2_RunTlsCallable.descriptors.1=PV_LIB_SPEC_PreludeValues14.fn93 ∨
      PV_THR2_RunTlsCallable.descriptors.1=PV_LIB_SPEC_StackSize14.token ∨
      PV_THR2_RunTlsCallable.descriptors.1=PV_THR2_Source361HookChildren.fnTrueFull ∨
      PV_THR2_RunTlsCallable.descriptors.1=PV_THR2_Source361HookChildren.fnFalseFull) from by tauto),
    PV_LIB_SPEC_PrefixEnvironment13.native,unselected,Bool.false_eq_true,if_false,
    show PV_THR2_OffPath.functionId PV_THR2_RunTlsCallable.descriptors.1 = none from rfl]
  rfl

#print axioms unforwarded
#print axioms unselected
#print axioms backend_pending
end PV_LIB_A_F5ClosurePending16

import PV_LIB_SPEC_Tls277Native15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls277Bound15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls277Native15 (token pointer value different pure native)
open PV_LIB_SPEC_TlsBound15 (parameters)

theorem trigger (resources : Resources) (w : OWNER) (a : Nat) (address : Address) :
    PV_THR2_OwnUniformResourceHandler.lift (parameters resources).environment.native (.child token a [pointer address]) w =
      ⟨.returned (.ok .null),w,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have n453 := different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl (by decide)
  have n454 := different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl (by decide)
  have n469 : token ≠ (PV_THR2_KeyValues.castToken false).2 := different _ 469 rfl (by decide)
  have n18 : token ≠ PV_THR2_F2Call.descriptors.2 := different _ 18 rfl (by decide)
  have tls : PV_LIB_SPEC_TlsBindings13.selected (.child token a [pointer address]) = false := by
    simp [PV_LIB_SPEC_TlsBindings13.selected,PV_THR2_FnOnceDispatch.request,n469,n18]
  simp only [PV_THR2_OwnUniformResourceHandler.lift,parameters,
    PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
    PV_LIB_SPEC_ReachedEnvironment14.native,
    if_neg (show ¬(token=PV_LIB_SPEC_RawVec14.token ∨ token=PV_LIB_SPEC_PreludeValues14.fn164 ∨
      token=PV_LIB_SPEC_PreludeValues14.fn165 ∨ token=PV_LIB_SPEC_PreludeValues14.fn93 ∨
      token=PV_LIB_SPEC_StackSize14.token ∨ token=PV_THR2_Source361HookChildren.fnTrueFull ∨
      token=PV_THR2_Source361HookChildren.fnFalseFull) from by tauto),
    PV_LIB_SPEC_PrefixEnvironment13.native,show PV_LIB_SPEC_TlsBindings13.selected
      (.child token a [pointer address]) = false from tls,if_false,
    show PV_THR2_OffPath.functionId token=some 277 from rfl]
  rfl

theorem answer (cut : PV_LIB_SPEC_ReachedNative14.Cut) (resources : Resources)
    (c : Config) (w : OWNER) (a : Nat) (address : Address)
    (wait : PV_STX2_Native.Waiting Data)
    (waiting : c.frame.waiting = some wait)
    (requested : wait.request = .child token a [pointer address]) :
    PV_LIB_SPEC_ReachedNative14.answer cut (parameters resources) c (.child token a [pointer address]) w =
      some ⟨.returned (.ok (value address)),w,[]⟩ := by
  apply PV_LIB_SPEC_Tls277Route15.route _ _ _ _ _ _ _ _ _ rfl
  unfold PV_LIB_SPEC_CallbackRuntime.answer PV_LIB_SPEC_CallbackRuntime.valueAnswer
  rw [native _ _ _ _ _ _ (trigger resources w a address)]
  simp only [show PV_THR2_OffPath.functionId token=some 277 from rfl,
    show ¬(some 277 = (some 360 : Option Nat)) from by decide,ite_false]
  have valid : PV_LIB_SPEC_CallbackRuntime.invalidPure (parameters resources) c w = false := by
    unfold PV_LIB_SPEC_CallbackRuntime.invalidPure
    simp only [waiting]
    rw [requested]
    simp only [show PV_THR2_OffPath.functionId token=some 277 from rfl,
      trigger resources w a address,pure,Option.isNone_some]
  rw [valid]
  simp only [Bool.false_eq_true,ite_false]
  change some (PV_LIB_SPEC_BoundRuntime.frameReply (.child token a [pointer address]) w
    ⟨.returned (.ok (value address)),w,[]⟩) = _
  unfold PV_LIB_SPEC_BoundRuntime.frameReply
  split <;> rfl

#print axioms trigger
#print axioms answer
end PV_LIB_SPEC_Tls277Bound15

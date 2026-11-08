import PV_LIB_A_ActiveGetter17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveTlsNative17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_EVHB_OwnerHeap
open PV_LIB_SPEC_TlsAt54 (token initValue)
open PV_LIB_SPEC_TlsNative15 (cut reference)

def request (a : Nat) : PV_STX2_Native.Request Data := .child token a [initValue]

def parameters (resources : Resources) : Parameters :=
  {PV_LIB_SPEC_ReachedEnvironment14.parameters with resources := resources}

theorem different (fn : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId fn = some id) (ne : 469≠id) : token ≠ fn := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 469 = PV_THR2_OffPath.functionId fn at same
  rw [number] at same
  exact ne (Option.some.inj same)

theorem selected (a : Nat) : PV_LIB_SPEC_TlsBindings13.selected (request a) = true := by
  classical
  change decide (token = token ∨ token = PV_THR2_F2Call.descriptors.2) = true
  simp only [true_or,eq_self,decide_true]

theorem trigger (resources : Resources) (w : OWNER) (a : Nat) :
    PV_THR2_OwnUniformResourceHandler.lift (parameters resources).environment.native (request a) w =
      ⟨.returned (.ok .null),w,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have n453 := different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl (by decide)
  have n454 := different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl (by decide)
  simp only [PV_THR2_OwnUniformResourceHandler.lift,parameters,
    PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
    PV_LIB_SPEC_ReachedEnvironment14.native,request,
    if_neg (show ¬(token=PV_LIB_SPEC_RawVec14.token ∨ token=PV_LIB_SPEC_PreludeValues14.fn164 ∨
      token=PV_LIB_SPEC_PreludeValues14.fn165 ∨ token=PV_LIB_SPEC_PreludeValues14.fn93 ∨
      token=PV_LIB_SPEC_StackSize14.token ∨ token=PV_THR2_Source361HookChildren.fnTrueFull ∨
      token=PV_THR2_Source361HookChildren.fnFalseFull) from by tauto),
    PV_LIB_SPEC_PrefixEnvironment13.native,show PV_LIB_SPEC_TlsBindings13.selected
      (.child token a [initValue]) = true from selected a,if_true]
  rfl

/-- At the reached request, allocationResources may be rebound to its actual
origin. TLS semantics ignores that resource field and computes the reference
from the SAME source/physical ACTIVE binding. No fresh entry world is used. -/
theorem answer (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (c : Config) (w : OWNER) (a : Nat)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot (parameters resources) c w = some false) :
    PV_LIB_SPEC_ReachedNative14.answer (cut stack) (parameters resources) c (request a) w =
    some ⟨.returned (.ok reference),w,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have n453 := different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl (by decide)
  have n454 := different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl (by decide)
  have id : PV_THR2_OffPath.functionId token = some 469 := rfl
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    request,if_neg n268,PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    if_neg n164,if_neg n165,if_neg n93,PV_LIB_SPEC_PrefixNative14.answer,
    PV_LIB_SPEC_PrefixNative14.core,if_neg n295,if_neg n454,if_neg n453,
    PV_LIB_SPEC_PrefixNative13.answer,PV_LIB_SPEC_PrefixNative13.core,id,
    show ¬(some 469 = (some 269 : Option Nat)) from by decide,ite_false,PV_LIB_SPEC_BoundNative13.answer,PV_LIB_SPEC_BoundNative13.core,
    PV_LIB_SPEC_Native13.answer,PV_LIB_SPEC_Native13.core,
    show PV_LIB_SPEC_TlsBindings13.selected (.child token a [initValue]) = true from selected a,
    Bool.true_eq,ite_true,cut]
  have bound : PV_LIB_SPEC_TlsBindings13.reply PV_LIB_SPEC_Entry13.slot
      (parameters resources) c w (request a)
      (PV_THR2_OwnUniformResourceHandler.lift (parameters resources).environment.native (request a)
        w) =
      some ⟨.returned (.ok reference),w,[]⟩ := by
    rw [trigger]
    unfold PV_LIB_SPEC_TlsBindings13.reply
    have value : PV_LIB_SPEC_TlsBindings13.value PV_LIB_SPEC_Entry13.slot
        (parameters resources) c w (request a) = some reference :=
      by
        unfold PV_LIB_SPEC_TlsBindings13.value
        simp only [request,token,PV_THR2_FnOnceDispatch.request,ite_true]
        have initializer : (runtime (parameters resources)).control.variant initValue = some 0 := rfl
        rw [initializer]
        change (do let _ ← PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
                     (parameters resources) c w
                   pure reference) = _
        rw [active]
        rfl
    rw [value]
    rfl
  simp only [request] at bound
  rw [bound]
  cases marked : PV_LIB_SPEC_BoundRuntime.allocationToken (request a) <;>
    simp only [request] at marked <;>
    simp only [Option.map_some,PV_LIB_SPEC_BoundRuntime.frameReply,marked,
      Bool.false_eq_true,ite_false,ite_true] <;> rfl

#print axioms parameters
#print axioms different
#print axioms selected
#print axioms trigger
#print axioms answer
end PV_LIB_A_ActiveTlsNative17

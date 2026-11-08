import PV_LIB_SPEC_NativePoll20
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_SPEC_Stack295Route20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_StackSize14 (token)

def bound (resources : Resources) : Parameters :=
  {PV_LIB_SPEC_ReachedEnvironment14.parameters with resources := resources}

theorem different (fn : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId fn = some id) (ne : 295≠id) : token ≠ fn := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 295 = PV_THR2_OffPath.functionId fn at same
  rw [number] at same
  exact ne (Option.some.inj same)

/-- The concrete environment chooses a successful execution arm; its marker
is not the returned stack size. The adapter computes the entire actual value. -/
theorem trigger (resources : Resources) (w : OWNER) (a : Nat) (args : List Data) :
    PV_THR2_OwnUniformResourceHandler.lift (bound resources).environment.native (.child token a args) w =
      ⟨.returned (.ok .null),w,[]⟩ := by
  classical
  simp only [PV_THR2_OwnUniformResourceHandler.lift,bound,
    PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
    PV_LIB_SPEC_ReachedEnvironment14.native]
  simp only [eq_self,true_or,or_true,ite_true]
  rfl

/-- Complete295 answer at an arbitrary reached context. `computed` is a local
value-law interface, discharged from source operands and actual cache below;
no native-success or desired source Store enters a machine specification. -/
theorem answer (cut : PV_LIB_SPEC_ReachedNative14.Cut) (resources : Resources)
    (c : Config) (w : OWNER) (a : Nat) (args : List Data) (v : Data)
    (computed : PV_LIB_SPEC_StackSize14.value (bound resources) w args = some v) :
    PV_LIB_SPEC_ReachedNative14.answer cut (bound resources) c (.child token a args) w =
      some ⟨.returned (.ok v),w,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,if_neg n268,
    PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,if_neg n164,if_neg n165,if_neg n93,
    PV_LIB_SPEC_PrefixNative14.answer,PV_LIB_SPEC_PrefixNative14.core,ite_true,
    trigger,PV_LIB_SPEC_StackSize14.reply,computed,Option.map_some]
  have framed (req : PV_STX2_Native.Request Data) :
      PV_LIB_SPEC_BoundRuntime.frameReply req w ⟨.returned (.ok v),w,[]⟩ =
        ⟨.returned (.ok v),w,[]⟩ := by
    unfold PV_LIB_SPEC_BoundRuntime.frameReply
    split <;> rfl
  simp only [framed]

#print axioms bound
#print axioms different
#print axioms trigger
#print axioms answer
end PV_LIB_SPEC_Stack295Route20

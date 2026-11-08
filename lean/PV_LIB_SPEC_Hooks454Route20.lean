import PV_LIB_SPEC_Stack295Route20
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_SPEC_Hooks454Route20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Stack295Route20 (bound)
abbrev token := PV_THR2_Source361HookChildren.fnFalseFull

theorem different (fn : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId fn = some id) (ne : 454≠id) : token ≠ fn := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 454 = PV_THR2_OffPath.functionId fn at same
  rw [number] at same
  exact ne (Option.some.inj same)

theorem trigger (resources : Resources) (w : OWNER) (a : Nat) (args : List Data) :
    PV_THR2_OwnUniformResourceHandler.lift (bound resources).environment.native (.child token a args) w =
      ⟨.returned (.ok .null),w,[]⟩ := by
  classical
  simp only [PV_THR2_OwnUniformResourceHandler.lift,bound,
    PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
    PV_LIB_SPEC_ReachedEnvironment14.native]
  simp only [eq_self,true_or,or_true,ite_true]
  rfl

/-- Complete454 answer, retaining the actual Thread source argument, the
initialized-empty TLS check and the binary's exact32 stack stores. The two
local read interfaces are proved from the reached pre-world by consumers. -/
theorem answer (cut : PV_LIB_SPEC_ReachedNative14.Cut) (resources : Resources)
    (c : Config) (w : OWNER) (a : Nat) (args : List Data) (threadPointer : Nat)
    (thread : PV_LIB_SPEC_SpawnHooks14.thread (bound resources) c w args = some threadPointer)
    (empty : PV_LIB_SPEC_SpawnHooks14.empty cut.hooksSlot w = some ()) :
    PV_LIB_SPEC_ReachedNative14.answer cut (bound resources) c (.child token a args) w =
      some ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
        PV_LIB_SPEC_PhysicalStack12.installDefault cut.native.memory.stack w,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,if_neg n268,
    PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,if_neg n164,if_neg n165,if_neg n93,
    PV_LIB_SPEC_PrefixNative14.answer,PV_LIB_SPEC_PrefixNative14.core,if_neg n295,ite_true,
    trigger,PV_LIB_SPEC_SpawnHooks14.reply,thread,empty]
  change some (PV_LIB_SPEC_BoundRuntime.frameReply (.child token a args) w
    (PV_LIB_SPEC_BoundRuntime.frameReply (.child token a args) w
      (PV_LIB_SPEC_BoundRuntime.frameReply (.child token a args) w
        ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
          PV_LIB_SPEC_PhysicalStack12.installDefault cut.native.memory.stack w,[]⟩))) = _
  have framed (req : PV_STX2_Native.Request Data) :
      PV_LIB_SPEC_BoundRuntime.frameReply req w
        ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
          PV_LIB_SPEC_PhysicalStack12.installDefault cut.native.memory.stack w,[]⟩ =
        ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
          PV_LIB_SPEC_PhysicalStack12.installDefault cut.native.memory.stack w,[]⟩ := by
    unfold PV_LIB_SPEC_BoundRuntime.frameReply
    split <;> rfl
  simp only [framed]

#print axioms token
#print axioms different
#print axioms trigger
#print axioms answer
end PV_LIB_SPEC_Hooks454Route20

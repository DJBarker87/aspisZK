import PV_LIB_SPEC_ReachedEnvironment14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AssembledChecks14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_NativeChecks14 (config arguments)
open PV_LIB_SPEC_Entry14 (state hooksSlot)

def cut (native : PV_LIB_SPEC_Native13.Cut) : PV_LIB_SPEC_ReachedNative14.Cut := ⟨native,hooksSlot⟩

theorem different (fn : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId fn = some id) (ne : 454≠id) :
    PV_THR2_Source361HookChildren.fnFalseFull ≠ fn := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 454 = PV_THR2_OffPath.functionId fn at same
  rw [number] at same
  exact ne (Option.some.inj same)

/-- FULL final assembly at the exact f454 token and source &Thread shape.
The actual byte image survives every all-answer ghost frame. This is a local
poll on the complete entry world, not original-entry reachability of this poll. -/
theorem f454 (native : PV_LIB_SPEC_Native13.Cut) (a : Nat) :
    PV_LIB_SPEC_ReachedNative14.answer (cut native) PV_LIB_SPEC_ReachedEnvironment14.parameters
      config (.child PV_THR2_Source361HookChildren.fnFalseFull a arguments) state =
    some ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
      PV_LIB_SPEC_PhysicalStack12.installDefault native.memory.stack state,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have trigger : PV_THR2_OwnUniformResourceHandler.lift
      PV_LIB_SPEC_ReachedEnvironment14.parameters.environment.native
      (.child PV_THR2_Source361HookChildren.fnFalseFull a arguments) state =
      ⟨.returned (.ok .null),state,[]⟩ := by
    simp [PV_THR2_OwnUniformResourceHandler.lift,
      PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
      PV_LIB_SPEC_ReachedEnvironment14.native]
    rfl
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    if_neg n268,PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    if_neg n164,if_neg n165,if_neg n93,PV_LIB_SPEC_PrefixNative14.answer,
    PV_LIB_SPEC_PrefixNative14.core,if_neg n295,ite_true,cut,trigger]
  have bound : PV_LIB_SPEC_SpawnHooks14.reply native.memory.stack hooksSlot
      PV_LIB_SPEC_ReachedEnvironment14.parameters config state arguments
      ⟨.returned (.ok .null),state,[]⟩ =
      some ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
        PV_LIB_SPEC_PhysicalStack12.installDefault native.memory.stack state,[]⟩ := by
    have source : PV_LIB_SPEC_SpawnHooks14.thread PV_LIB_SPEC_ReachedEnvironment14.parameters
        config state arguments = some 16384 := PV_LIB_SPEC_NativeChecks14.thread_value
    unfold PV_LIB_SPEC_SpawnHooks14.reply
    rw [source]
    change (do let _ ← PV_LIB_SPEC_SpawnHooks14.empty hooksSlot state
               pure (PV_LIB_SPEC_SpawnHooks14.result native.memory.stack state
                 (⟨.returned (.ok .null),state,[]⟩ : Reply OWNER Event Data))) = _
    rw [PV_LIB_SPEC_NativeChecks14.empty_tls]
    rfl
  rw [bound]
  cases marked : PV_LIB_SPEC_BoundRuntime.allocationToken
      (.child PV_THR2_Source361HookChildren.fnFalseFull a arguments) <;>
    simp only [Option.map_some,PV_LIB_SPEC_BoundRuntime.frameReply,marked,
      Bool.false_eq_true,ite_false,ite_true] <;> rfl

#print axioms cut
#print axioms different
#print axioms f454
end PV_LIB_SPEC_AssembledChecks14

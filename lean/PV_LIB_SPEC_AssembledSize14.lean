import PV_LIB_SPEC_AssembledChecks14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AssembledSize14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Entry14 (state)

def arguments : List Data :=
  [PV_THR2_KeyValues.pack PV_LIB_SPEC_Builder269.sizeKind [],
   PV_THR2_KeyValues.pack PV_LIB_SPEC_StackSize14.closureKind []]

theorem different (fn : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId fn = some id) (ne : 295≠id) :
    PV_LIB_SPEC_StackSize14.token ≠ fn := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 295 = PV_THR2_OffPath.functionId fn at same
  rw [number] at same
  exact ne (Option.some.inj same)

/-- Exact12111 token/None/closure operands, through the FULL final assembly.
The2MiB value comes from the actual cached word. This is a local binding
check; it does not assert original reachability of12111. -/
theorem f295 (cut : PV_LIB_SPEC_ReachedNative14.Cut) (c : Config) (a : Nat) :
    PV_LIB_SPEC_ReachedNative14.answer cut PV_LIB_SPEC_ReachedEnvironment14.parameters
      c (.child PV_LIB_SPEC_StackSize14.token a arguments) state =
    some ⟨.returned (.ok (.number 2097152)),state,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have trigger : PV_THR2_OwnUniformResourceHandler.lift
      PV_LIB_SPEC_ReachedEnvironment14.parameters.environment.native
      (.child PV_LIB_SPEC_StackSize14.token a arguments) state =
      ⟨.returned (.ok .null),state,[]⟩ := by
    simp [PV_THR2_OwnUniformResourceHandler.lift,
      PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
      PV_LIB_SPEC_ReachedEnvironment14.native]
    rfl
  have size : PV_LIB_SPEC_StackSize14.value PV_LIB_SPEC_ReachedEnvironment14.parameters
      state arguments = some (.number 2097152) := PV_LIB_SPEC_NativeChecks14.size_value
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    if_neg n268,PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    if_neg n164,if_neg n165,if_neg n93,PV_LIB_SPEC_PrefixNative14.answer,
    PV_LIB_SPEC_PrefixNative14.core,ite_true,trigger,PV_LIB_SPEC_StackSize14.reply,size]
  rfl

#print axioms arguments
#print axioms different
#print axioms f295
end PV_LIB_SPEC_AssembledSize14

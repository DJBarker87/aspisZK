import PV_LIB_SPEC_ActiveAdoption19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveNative19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerHeap
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsBound15 (parameters)
open PV_LIB_SPEC_TlsNative15 (cut reference)
abbrev token := PV_FN_THREAD_f207.fn289
def request (a : Nat) : PV_STX2_Native.Request Data := .child token a [reference,.boolean true]

theorem different (fn : Data) (id : Nat)
    (number : PV_THR2_OffPath.functionId fn = some id) (ne : 289 ≠ id) : token ≠ fn := by
  intro eq
  have same := congrArg PV_THR2_OffPath.functionId eq
  change some 289 = PV_THR2_OffPath.functionId fn at same
  rw [number] at same
  exact ne (Option.some.inj same)

theorem not_tls (a : Nat) : PV_LIB_SPEC_TlsBindings13.selected (request a) = false := by
  classical
  have n469 := different (PV_THR2_KeyValues.castToken false).2 469 rfl (by decide)
  have n18 := different PV_THR2_F2Call.descriptors.2 18 rfl (by decide)
  change decide (token = (PV_THR2_KeyValues.castToken false).2 ∨
    token = PV_THR2_F2Call.descriptors.2) = false
  simp only [n469,n18,or_self,decide_false]

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
    PV_LIB_SPEC_PrefixEnvironment13.native,
    show PV_LIB_SPEC_TlsBindings13.selected (.child token a [reference,.boolean true]) = false from not_tls a,
    Bool.false_eq_true,ite_false]
  rfl

/-- Exact native8248 semantics inside the contracted207. Neither a successful
native reply nor a desired Store delta is a binder; false is read in both models.
Actual outer8162 reachability remains a separate same-history obligation. -/
theorem answer (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (c : Config) (w : OWNER) (a : Nat)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (parameters resources) c w = some false) :
    PV_LIB_SPEC_ReachedNative14.answer (cut stack) (parameters resources) c (request a) w =
      some ⟨.returned (.ok (.boolean false)),
        PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true,[]⟩ := by
  classical
  have n268 := different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have n453 := different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl (by decide)
  have n454 := different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl (by decide)
  have id : PV_THR2_OffPath.functionId token = some 289 := rfl
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    request,if_neg n268,PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    if_neg n164,if_neg n165,if_neg n93,PV_LIB_SPEC_PrefixNative14.answer,
    PV_LIB_SPEC_PrefixNative14.core,if_neg n295,if_neg n454,if_neg n453,
    PV_LIB_SPEC_PrefixNative13.answer,PV_LIB_SPEC_PrefixNative13.core,id,
    show ¬(some 289 = (some 269 : Option Nat)) from by decide,ite_false,
    PV_LIB_SPEC_BoundNative13.answer,PV_LIB_SPEC_BoundNative13.core,cut]
  have bound := PV_LIB_SPEC_ActiveReplacement16.physical (parameters resources) c w active
  rw [show PV_THR2_OwnUniformResourceHandler.lift (parameters resources).environment.native
    (.child token a [reference,.boolean true]) w = ⟨.returned (.ok .null),w,[]⟩ from trigger resources w a]
  rw [bound]
  simp only [Option.map_some,PV_LIB_SPEC_BoundRuntime.frameReply,
    PV_LIB_SPEC_BoundRuntime.allocationToken,Bool.false_eq_true,ite_false]
  rfl

#print axioms token
#print axioms request
#print axioms different
#print axioms not_tls
#print axioms trigger
#print axioms answer
end PV_LIB_SPEC_ActiveNative19

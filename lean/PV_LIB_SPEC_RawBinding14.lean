import PV_LIB_SPEC_AssembledSize14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_RawBinding14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- SPEC-C12 local dispatch check: the164 adapter is dormant in the actual
FULL resolver. Its waiting configuration is handled as a BODY push, never
as a native164 poll. No original reachability is asserted here. -/
theorem inline164 (s : Store Data) (a child : Nat) (parents : List Frame) :
    PV_LIB_StoreActionTable.select PV_LIB_SPEC_Full.programs
      ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5,
        waiting := some ⟨.child PV_LIB_SPEC_PreludeValues14.fn164 child [],
          .child child (.local 4),[]⟩},parents,s⟩ = none := by
  let wait : PV_STX2_Native.Waiting Data :=
    ⟨.child PV_LIB_SPEC_PreludeValues14.fn164 child [],.child child (.local 4),[]⟩
  change (match PV_LIB_SPEC_Full.programs PV_LIB_SPEC_PreludeValues14.fn164 with
    | some _ => none
    | none => (PV_LIB_StoreActionTable.v2 PV_LIB_SPEC_PreludeValues14.fn164).bind
        (fun action => some (⟨action,PV_LIB_SPEC_PreludeValues14.fn164,wait,[]⟩ : PV_LIB_StoreActionTable.Site))) = none
  rw [PV_LIB_SPEC_RawVec14.dispatch.1]

theorem at268 (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (w : OWNER) (a : Nat) :
    PV_LIB_SPEC_ReachedNative14.core cut p c (.child PV_LIB_SPEC_RawVec14.token a []) w =
      some (PV_LIB_SPEC_RawVec14.reply w
        (PV_THR2_OwnUniformResourceHandler.lift p.environment.native
          (.child PV_LIB_SPEC_RawVec14.token a []) w)) := by
  classical
  simp only [PV_LIB_SPEC_ReachedNative14.core,ite_true]

/-- Repair at the actual7894 token, through the final handler and its frame.
No opaque marker is mistaken for the RawVec; native268 returns the empty
source header whose fields were checked in RawVec14.fields. -/
theorem bound268 (cut : PV_LIB_SPEC_ReachedNative14.Cut) (c : Config) (w : OWNER) (a : Nat) :
    PV_LIB_SPEC_ReachedNative14.answer cut PV_LIB_SPEC_ReachedEnvironment14.parameters c
      (.child PV_LIB_SPEC_RawVec14.token a []) w =
      some ⟨.returned (.ok PV_LIB_SPEC_RawVec14.value),w,[]⟩ := by
  classical
  have trigger : PV_THR2_OwnUniformResourceHandler.lift
      PV_LIB_SPEC_ReachedEnvironment14.parameters.environment.native
      (.child PV_LIB_SPEC_RawVec14.token a []) w = ⟨.returned (.ok .null),w,[]⟩ := by
    simp [PV_THR2_OwnUniformResourceHandler.lift,
      PV_LIB_SPEC_ReachedEnvironment14.parameters,PV_LIB_SPEC_ReachedEnvironment14.environment,
      PV_LIB_SPEC_ReachedEnvironment14.native]
    rfl
  unfold PV_LIB_SPEC_ReachedNative14.answer
  rw [at268,trigger]
  rfl

#print axioms inline164
#print axioms at268
#print axioms bound268
end PV_LIB_SPEC_RawBinding14

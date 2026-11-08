import PV_LIB_A_F17ValueLift16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F17History16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def store : Store Data := write (write PV_LIB_A_F170Return16.store ⟨5,0,[]⟩
  (some PV_LIB_A_F170Return16.value)) ⟨4,3,[]⟩ (some PV_LIB_A_F170Return16.value)
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage (PV_THR2_RunWithValue.prepared store 4 (.boolean false)) 4
    PV_LIB_SPEC_TlsOriginal14.withParents (PV_THR2_F17.live.body.drop 15) e.world [] [] []).state

theorem cell : store.cells ⟨4,3,[]⟩ =
    some (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [.boolean false]) := by
  simp [store,PV_LIB_A_F170Return16.value,PV_LIB_A_F170Result16.kind,PV_THR2_RunTlsReturn.kind,write] <;> rfl

theorem original104 (e : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e activation 104).state = after e := by
  let cut := PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation)
  let H : Handler := fun _ w => ⟨.pending,w,[]⟩
  let q := PV_LIB_SPEC_LaneAJoins18.history e activation 96
  have hq : q = stage store 4 PV_LIB_SPEC_TlsOriginal14.withParents
      (PV_THR2_F17.live.body.drop 7) e.world [] q.issued q.consumed := by
    apply PV_LIB_A_F170Return16.execution_ext
    · have hs := PV_LIB_A_F170Return16.original96 e activation
      change q.state = _ at hs
      dsimp only [PV_LIB_A_F170Return16.after,PV_LIB_A_Return16.delivered,
        PV_LIB_A_F170Return16.saved,PV_THR2_F17Call.parent,stage,store] at hs ⊢
      exact hs
    · simp only [stage]
    · simp only [stage]
  have trace := PV_LIB_A_F17Value16.trace cut PV_LIB_SPEC_ReachedEnvironment14.parameters H
    store 4 PV_LIB_SPEC_TlsOriginal14.withParents (.boolean false) e.world [] q.issued q.consumed cell
  have existing := PV_LIB_A_F17ValueLift16.source PV_LIB_SPEC_ReachedEnvironment14.parameters H
    store 4 PV_LIB_SPEC_TlsOriginal14.withParents (.boolean false) e.world [] cell
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 104
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [show 104=96+8 from rfl,PV_LIB_SPEC_Original14.run_add]
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 8 q).state = _
  rw [hq]
  exact PV_LIB_SPEC_SourceProjection15.transport cut _ H 8 _ (after e) trace existing

#print axioms cell
#print axioms original104
end PV_LIB_A_F17History16

import PV_LIB_A_F17Finish16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F17Return16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def store : Store Data := PV_THR2_RunWithValue.prepared PV_LIB_A_F17History16.store 4 (.boolean false)
def saved : Frame := PV_THR2_F2Child.parent PV_LIB_SPEC_TlsOriginal14.workerStore 3 PV_THR2_F2Call.descriptors.2
def wait : PV_STX2_Native.Waiting Data :=
  ⟨.child PV_THR2_F2Call.descriptors.1 4 [PV_STX2_TypedReferences.reference ⟨3,2,[]⟩ .null,
    PV_THR2_F2Call.descriptors.2],.child 4 (.local 0),[]⟩
def returnedStore : Store Data := write (write (PV_THR2_RunWithReturn.prepared store 4)
  ⟨4,0,[]⟩ (some (.boolean false))) ⟨3,0,[]⟩ (some (.boolean false))
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage returnedStore 3 PV_LIB_SPEC_TlsOriginal14.workerParents
    (PV_THR2_F2.live.body.drop 6) e.world [] [] []).state

theorem cell : store.cells ⟨4,0,[]⟩ = some (.boolean false) :=
  PV_THR2_RunWithReturn.cell _ _ _

theorem original112 (e : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e activation 112).state = after e := by
  let cut := PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation)
  let H : Handler := fun _ w => ⟨.pending,w,[]⟩
  let q := PV_LIB_SPEC_LaneAJoins18.history e activation 104
  have hq : q = stage store 4 (saved::PV_LIB_SPEC_TlsOriginal14.workerParents)
      (PV_THR2_F17.live.body.drop 15) e.world [] q.issued q.consumed := by
    apply PV_LIB_A_F170Return16.execution_ext
    · have hs := PV_LIB_A_F17History16.original104 e activation
      change q.state = _ at hs
      dsimp only [PV_LIB_A_F17History16.after,store,saved,
        PV_LIB_SPEC_TlsOriginal14.withParents,stage] at hs ⊢
      exact hs
    · simp only [stage]
    · simp only [stage]
  have returned := PV_LIB_A_F17Finish16.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters H
    store 4 saved PV_LIB_SPEC_TlsOriginal14.workerParents wait (.boolean false) e.world []
    q.issued q.consumed cell (show saved.waiting = some wait from rfl) rfl
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 112
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [show 112=104+8 from rfl,PV_LIB_SPEC_Original14.run_add]
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 8 q).state = _
  rw [hq]
  simpa only [after,stage,returnedStore,saved,PV_THR2_F2Child.parent] using returned

#print axioms cell
#print axioms original112
end PV_LIB_A_F17Return16

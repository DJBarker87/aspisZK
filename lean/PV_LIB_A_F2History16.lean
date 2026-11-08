import PV_LIB_A_F2Finish16
import PV_LIB_A_HistoryExtend16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F2History16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def store : Store Data := PV_LIB_A_F17Return16.returnedStore
def saved : Frame := PV_THR2_F1Worker.parent PV_LIB_SPEC_Worker14.store 2
def wait : PV_STX2_Native.Waiting Data := ⟨.child PV_THR2_Table.workerCallee 3 [],.child 3 (.local 9),[]⟩
def returnedStore : Store Data := PV_THR2_RunWorkerReturn.stored store 3 saved (.boolean false)
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage returnedStore 2 PV_LIB_SPEC_F1Arithmetic14.parents (PV_THR2_F1.live.body.drop 12)
    e.world [] [] []).state

theorem cell : store.cells ⟨3,0,[]⟩ = some (.boolean false) := by
  simp [store,PV_LIB_A_F17Return16.returnedStore,write]

theorem original116 (e : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e activation 116).state = after e := by
  apply PV_LIB_A_HistoryExtend16.extend e activation 112 4 store 3
    (saved::PV_LIB_SPEC_F1Arithmetic14.parents) (PV_THR2_F2.live.body.drop 6) (after e)
  · simpa only [PV_LIB_A_F17Return16.after,store,saved,PV_LIB_SPEC_TlsOriginal14.workerParents,stage]
      using PV_LIB_A_F17Return16.original112 e activation
  · intro issued consumed
    have returned := PV_LIB_A_F2Finish16.run
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters (fun _ w => ⟨.pending,w,[]⟩)
      store 3 saved PV_LIB_SPEC_F1Arithmetic14.parents wait (.boolean false) e.world []
      issued consumed cell (show saved.waiting = some wait from rfl) rfl
    simpa only [after,stage,returnedStore,saved,PV_THR2_F1Worker.parent] using returned

#print axioms cell
#print axioms original116
end PV_LIB_A_F2History16

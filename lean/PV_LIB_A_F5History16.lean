import PV_LIB_A_F5Prefix16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F5History16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def activation : Nat := PV_LIB_A_F2History16.returnedStore.nextActivation
def store : Store Data := PV_THR2_RunActiveEntry.issued
  (PV_LIB_A_F5Entry16.branchStore PV_LIB_A_F2History16.returnedStore 2) 2
def parents : List Frame := PV_THR2_RunActiveEntry.parent
  (PV_LIB_A_F5Entry16.branchStore PV_LIB_A_F2History16.returnedStore 2) 2 :: PV_LIB_SPEC_F1Arithmetic14.parents

def at123 (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage store activation parents PV_THR2_F5.live.body e.world [] [] []).state

theorem original123 (e : PV_LIB_SPEC_EntryWorld18.Entry) (frameActivation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e frameActivation 123).state = at123 e := by
  apply PV_LIB_A_HistoryExtend16.extend e frameActivation 116 7 PV_LIB_A_F2History16.returnedStore
    2 PV_LIB_SPEC_F1Arithmetic14.parents (PV_THR2_F1.live.body.drop 12) (at123 e)
  · exact PV_LIB_A_F2History16.original116 e frameActivation
  · intro issued consumed
    have segment := PV_LIB_A_F5Entry16.run
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e frameActivation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_A_F2History16.returnedStore
      2 PV_LIB_SPEC_F1Arithmetic14.parents e.world [] issued consumed (by
        simp [PV_LIB_A_F2History16.returnedStore,PV_THR2_RunWorkerReturn.stored,
          PV_LIB_A_F2History16.saved,PV_THR2_F1Worker.parent,write])
    simpa only [PV_LIB_A_F5Entry16.after,at123,store,activation,parents,stage]
      using congrArg Execution.state segment

def prepared : Store Data := PV_THR2_ActivePrefix.prepared store activation
  PV_LIB_SPEC_ReachedEnvironment14.parameters.needsDrop

def at131 (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage prepared activation parents (PV_THR2_F5.live.body.drop 8) e.world [] [] []).state

theorem original131 (e : PV_LIB_SPEC_EntryWorld18.Entry) (frameActivation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e frameActivation 131).state = at131 e := by
  apply PV_LIB_A_HistoryExtend16.extend e frameActivation 123 8 store activation parents
    PV_THR2_F5.live.body (at131 e)
  · exact original123 e frameActivation
  · intro issued consumed
    exact PV_LIB_A_F5Prefix16.run
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e frameActivation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters (fun _ w => ⟨.pending,w,[]⟩)
      store activation parents e.world [] issued consumed

#print axioms original123
#print axioms original131
end PV_LIB_A_F5History16

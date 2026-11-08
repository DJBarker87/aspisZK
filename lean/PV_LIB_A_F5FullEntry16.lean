import PV_LIB_A_F5FullPush16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F5FullEntry16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def keyAddress : Address := ⟨PV_LIB_A_F5History16.activation,3,[]⟩
def closure : Data := PV_THR2_KeyValues.pack PV_THR2_ActivePrefix.descriptors.2 []

theorem key_bound : PV_LIB_A_F5FullPush16.store.cells ⟨PV_LIB_A_F5FullPush16.activation,1,[]⟩ =
    some (PV_STX2_TypedReferences.reference keyAddress .null) := by
  simp [PV_LIB_A_F5FullPush16.store,PV_LIB_A_F5FullPush16.activation,PV_THR2_ActiveRequest.issued,
    PV_STX2_Native.arguments,write,keyAddress]

theorem closure_bound : PV_LIB_A_F5FullPush16.store.cells ⟨PV_LIB_A_F5FullPush16.activation,2,[]⟩ =
    some closure := by
  simp [PV_LIB_A_F5FullPush16.store,PV_LIB_A_F5FullPush16.activation,PV_THR2_ActiveRequest.issued,
    PV_STX2_Native.arguments,write,closure]

def store : Store Data := PV_THR2_F17Call.issued PV_LIB_A_F5FullPush16.store
  PV_LIB_A_F5FullPush16.activation keyAddress closure
def activation : Nat := PV_LIB_A_F5FullPush16.store.nextActivation
def parents : List Frame := PV_THR2_F17Call.parent PV_LIB_A_F5FullPush16.store
  PV_LIB_A_F5FullPush16.activation keyAddress closure :: PV_LIB_A_F5FullPush16.parents

def at141 (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage store activation parents PV_THR2_F170.live.body e.world [] [] []).state

theorem original141 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e a 141).state = at141 e := by
  apply PV_LIB_A_HistoryExtend16.extend e a 133 8 PV_LIB_A_F5FullPush16.store
    PV_LIB_A_F5FullPush16.activation PV_LIB_A_F5FullPush16.parents PV_THR2_F17.live.body (at141 e)
  · exact PV_LIB_A_F5FullPush16.original133 e a
  · intro issued consumed
    have segment := PV_LIB_SPEC_F17Entry14.enter
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
      PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_A_F5FullPush16.store
      PV_LIB_A_F5FullPush16.activation keyAddress closure PV_LIB_A_F5FullPush16.parents
      e.world [] issued consumed key_bound closure_bound
    simpa only [PV_LIB_SPEC_F17Entry14.after,at141,store,activation,parents,stage]
      using congrArg Execution.state segment

#print axioms key_bound
#print axioms closure_bound
#print axioms original141
end PV_LIB_A_F5FullEntry16

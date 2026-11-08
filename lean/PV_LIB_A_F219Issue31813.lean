import PV_LIB_A_CallIssue13
import PV_THR2_CatchChildren
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F219Issue31813
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

def programs := PV_THR2_CatchChildren.table
def src := PV_LIB_A_StructuredFrontier13.source PV_THR2_F219.node16
def rest := PV_THR2_F219.live.body.drop 17

theorem shape : PV_LIB_A_StructuredFrontier13.node src :: rest = PV_THR2_F219.live.body.drop 16 := rfl

def steps (C : Carrier OWNER Data) := PV_LIB_A_CallIssue13.steps src rest
def after (C : Carrier OWNER Data) := PV_LIB_A_CallIssue13.after C src rest

/-- Actual9196 issuance with every missing-operand case retained.
No captured value, child activation, successful native reply or desired store is supplied. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps C q) ⟨q,none⟩ = ⟨after C q,none⟩ := by
  apply PV_LIB_A_CallIssue13.run
  · decide
  · intro s a w; rfl

#print axioms programs
#print axioms shape
#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_F219Issue31813

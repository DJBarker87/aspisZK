import PV_LIB_A_StructuredFrontier13
import PV_THR2_SourceTraitDispatch
import PV_THR2_CatchTakeChild
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F220Enter20814
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

def programs (P : Data → Option PV_STX2_SliceSyntax.Program) := PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve P)
def src := PV_LIB_A_StructuredFrontier13.source PV_THR2_F220.node5
def rest := PV_THR2_F220.live.body.drop 6

theorem shape : PV_LIB_A_StructuredFrontier13.node src :: rest = PV_THR2_F220.live.body.drop 5 := rfl

def steps (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src rest
def after (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src rest PV_THR2_F208.live

/-- Actual emitted structured entry with every missing-operand case retained.
No captured value, child activation, successful native reply or desired store is supplied. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps C q) ⟨q,none⟩ = ⟨after C q,none⟩ := by
  apply PV_LIB_A_StructuredFrontier13.run
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    cases ids
  · intro s a w; rfl
  · rfl

#print axioms programs
#print axioms shape
#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_F220Enter20814

import PV_THR2_OwnInitHandlerCases
import PV_THR2_OwnInitAllocationCasesAtState
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitHandlerCasesAtState
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
actual operand's decoded case, the trace-derived retained frame, and
FreshAllocationValidity' at THIS pre-state. Generalize the existing
OwnInitHandlerCases interpretation past arbitrary clone214 backend effects;
never register a second time or move validity back across the clone. These
are local eliminator cases, not unexplained OwnInit closure hypotheses. -/
theorem allocation (pre : OWNER) (a id activation : Nat)
    (resources : Resources) (encode : Encode) (granted : GrantedRegions)
    (payload : Data) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (decoded : PV_THR2_OwnInitSourceCodec.decode payload = some words)
    (frame : PV_THR2_OwnUniformReceiverFrame.Frame a id
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) pre)
    (valid : FreshAllocationValidity' resources granted pre) :
    PV_THR2_OwnInitAllocationCases.Outcome ⟨a,[45]⟩ words
      (resources (.malloc 24) (world pre)).answer
      (PV_THR2_OwnInitAllocationHandler.handler resources encode fallback
        (.child PV_THR2_Source361InitChildren.fnAllocationFull activation [payload]) pre) := by
  have selected := PV_THR2_OwnInitAllocationSelection.selected frame
  simp only [PV_THR2_OwnInitAllocationHandler.handler,ite_true,decoded,selected.1,frame.header]
  exact PV_THR2_OwnInitAllocationCasesAtState.all pre a id resources encode granted words frame valid
#print axioms allocation
end PV_THR2_OwnInitHandlerCasesAtState

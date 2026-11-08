import PV_LIB_A_FetchSubRetry10
import PV_LIB_A_FetchSubPrefixes10
import PV_LIB_A_StrongCount10
import PV_LIB_A_GuardWeakBegin10
import PV_LIB_A_Payload24810
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary

/-- Public PARTIAL destruction-machine surface. Legacy v2 is retained exactly.
This name certifies neither complete D984 coverage nor caller-history adequacy. -/
abbrev DestructionState10 := PV_LIB_A_FetchSubMachine10.State

def v2DestructionPrograms10 := v2ProvenancePrograms

def v2DestructionStep10 := PV_LIB_A_FetchSubMachine10.step

def v2DestructionEntry10 := PV_LIB_A_FetchSubMachine10.wrap

/-- Original entry value carrier plus the exact builtin comparison needed by486.
The same previously installed aggregate fallback is applied by the step at its
native boundaries. Unknown custom allocators/dynamic destructors stay gaps. -/
def originalDestructionCarrier10 (C : Carrier OWNER Data) (b : Bool) :=
  PV_THR2_OwnInitExactReturnedCases.carrier (PV_LIB_A_ArcDropCompare10.numeric C) b

/-- Named access to the previous ONE symbolic local agreement. -/
theorem destruction_agreement10 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (phase : s.applied = none)
    (away : ∀ c, s.base.current.status = .running c → PV_LIB_A_FetchSubReply10.selected P c = none) :
    v2DestructionStep10 C K P resources encode H values (v2DestructionEntry10 s) =
      v2DestructionEntry10 (PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values s) :=
  PV_LIB_A_FetchSubMachine10.agreement C K P resources encode H values s phase away

#check v2
#print axioms v2DestructionPrograms10
#print axioms v2DestructionStep10
#print axioms v2DestructionEntry10
#print axioms originalDestructionCarrier10
#print axioms destruction_agreement10
end PV_LIB_StoreActionTable

import PV_LIB_Observation
import PV_W5_CopyContract
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceCopy
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_W5_CopyContract PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement

def model (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB.observe (⟨output H e w prior,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
def law (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop := out = model H e w prior stack

theorem certified (resources : Resources) (granted : GrantedRegions)
    (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) (pre : Pre resources e w)
    (fresh : FreshAllocationValidity' resources granted e.allocationEntry)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources) :
    law H e w prior stack (PV_LIB.observe (⟨output H e w prior,stack⟩ :
      PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧ Post H e w prior :=
  ⟨rfl,contract resources granted H e w prior pre fresh malloc_semantics⟩
#print axioms certified
end PV_LIB_SliceCopy

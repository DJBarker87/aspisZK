from pathlib import Path
sig='''(resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)''';args='resources encode base ctrl s parent parents a n w prior external backend'
text=f'''import PV_LIB_Observation
import PV_FN_SLICE_f31
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceCtor31
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner

def model {sig} (stack : List Config) :=
  PV_LIB.observe (⟨PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend,stack⟩ :
    PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
def law {sig} (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop := out = model {args} stack

theorem certified {sig} (stack : List Config)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects) :
    law {args} stack
      (PV_LIB.observe (⟨PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend,stack⟩ :
        PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧
    PV_FN_SLICE_f31.Post {args} :=
  ⟨rfl,PV_FN_SLICE_f31.contract resources encode base ctrl s parent parents a n w prior external backend effects
    pre malloc_semantics calloc_semantics drop_semantics⟩
#print axioms certified
end PV_LIB_SliceCtor31
''';Path('lean/PV_LIB_SliceCtor31.lean').write_text(text)
Path('lean/PV_LIB_SliceCopy.lean').write_text('''import PV_LIB_Observation
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
''')

import PV_LIB_Observation
import PV_FN_SLICE_f31
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceCtor31
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner

def model (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config) :=
  PV_LIB.observe (⟨PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend,stack⟩ :
    PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
def law (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop := out = model resources encode base ctrl s parent parents a n w prior external backend stack

theorem certified (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects) :
    law resources encode base ctrl s parent parents a n w prior external backend stack
      (PV_LIB.observe (⟨PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend,stack⟩ :
        PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧
    PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend :=
  ⟨rfl,PV_FN_SLICE_f31.contract resources encode base ctrl s parent parents a n w prior external backend effects
    pre malloc_semantics calloc_semantics drop_semantics⟩
#print axioms certified
end PV_LIB_SliceCtor31

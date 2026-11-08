import PV_LIB_Observation
import PV_FN_SLICE_f35
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceCtor35
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_FN_SLICE_f35

def result (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (zeroed : Bool) (alloc : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) := outcome resources encode base K s parent parents a n zeroed alloc w prior external backend
def actual (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (zeroed : Bool) (alloc : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) :=
  let H := handler resources encode base K s (parent::parents) a n zeroed external backend
  PV_STX2_Source7IterationBindings.advance resources encode (PV_W5_F35Constructors.C base K H)
    (PV_W5_F35Modes.L K) (fun _ => none) H (result resources encode base K s parent parents a n zeroed alloc w prior external backend).1
      (PV_W5_F35Entry.start s (parent::parents) a w prior)
def model (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (zeroed : Bool) (alloc : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config) :=
  PV_LIB.observe (⟨(result resources encode base K s parent parents a n zeroed alloc w prior external backend).2,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
def law (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (zeroed : Bool) (alloc : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop := out = model resources encode base K s parent parents a n zeroed alloc w prior external backend stack

theorem certified (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (zeroed : Bool) (alloc : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : Pre s (parent::parents) a n zeroed alloc w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects) :
    law resources encode base K s parent parents a n zeroed alloc w prior external backend stack
      (PV_LIB.observe (⟨actual resources encode base K s parent parents a n zeroed alloc w prior external backend,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧
    Post resources encode base K s parent parents a n zeroed alloc w prior external backend := by
  have h := contract resources encode base K s parent parents a n zeroed alloc w prior external backend effects pre malloc_semantics calloc_semantics drop_semantics
  refine ⟨?_,h⟩
  exact congrArg (fun q : Prefix OWNER PV_RJ4IDB.NativeEvent =>
    PV_LIB.observe (⟨q,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) h.2.1
#print axioms certified
end PV_LIB_SliceCtor35

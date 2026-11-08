import PV_LIB_Observation
import PV_FN_SLICE_f59
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceAlloc59
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_W5_F59Contract

def result (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (zeroed : Bool) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) :=
  let H := handler resources encode s parents a bytes external backend
  outcome resources encode (carrier base K H) s parents a bytes zeroed w prior external

def actual (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (zeroed : Bool) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) :=
  let H := handler resources encode s parents a bytes external backend
  PV_STX2_Source7IterationBindings.advance resources encode (carrier base K H) K
    PV_W5_F59PreludeReply.programs H (result resources encode base K s parents a bytes zeroed w prior external backend).1 (start s parents a w prior)

def model (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (zeroed : Bool) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config) :=
  PV_LIB.observe (⟨(result resources encode base K s parents a bytes zeroed w prior external backend).2,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
def law (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (zeroed : Bool) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model resources encode base K s parents a bytes zeroed w prior external backend stack

theorem certified (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (zeroed : Bool) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (pre : PV_FN_SLICE_f59.Pre s parents a bytes zeroed w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources) :
    law resources encode base K s parents a bytes zeroed w prior external backend stack
      (PV_LIB.observe (⟨actual resources encode base K s parents a bytes zeroed w prior external backend,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧
    PV_FN_SLICE_f59.Post resources encode base K s parents a bytes zeroed w prior external backend := by
  have h := PV_FN_SLICE_f59.contract resources encode base K s parents a bytes zeroed w prior external backend pre malloc_semantics calloc_semantics
  refine ⟨?_,h⟩
  exact congrArg (fun q : Prefix OWNER PV_RJ4IDB.NativeEvent =>
    PV_LIB.observe (⟨q,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) h.1
#print axioms certified
end PV_LIB_SliceAlloc59

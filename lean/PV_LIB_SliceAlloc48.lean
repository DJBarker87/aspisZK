import PV_LIB_Observation
import PV_FN_SLICE_f48
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceAlloc48
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_FN_SLICE_f48

def result (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) :=
  outcome s parents a (PV_STX2_Source7AllocationRuntimeEntry.layout bytes 4) prior
    (reply resources encode base K s parents a bytes w external backend)

def actual (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) :=
  advance (PV_STX2_Source7CapacityScalars.carrier base) K (fun _ => none)
    (handler resources encode base K s parents a bytes external backend)
    (result resources encode base K s parents a bytes w prior external backend).1 (start s parents a w prior)

def model (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config) :=
  PV_LIB.observe (⟨(result resources encode base K s parents a bytes w prior external backend).2,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)

def law (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model resources encode base K s parents a bytes w prior external backend stack

theorem certified (resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (stack : List Config)
    (pre : Pre s parents a bytes w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources) :
    law resources encode base K s parents a bytes w prior external backend stack
      (PV_LIB.observe (⟨actual resources encode base K s parents a bytes w prior external backend,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧
    Post resources encode base K s parents a bytes w prior external backend := by
  have h := contract resources encode base K s parents a bytes w prior external backend pre malloc_semantics calloc_semantics
  refine ⟨?_,h⟩
  change PV_LIB.observe (⟨actual resources encode base K s parents a bytes w prior external backend,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) = _
  unfold actual result
  rw [h.1]
  rfl
#print axioms certified
end PV_LIB_SliceAlloc48

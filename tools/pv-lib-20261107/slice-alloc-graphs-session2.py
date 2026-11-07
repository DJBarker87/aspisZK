from pathlib import Path
for n in [47,48]:
 ns=f'PV_LIB_SliceAlloc{n}'; root=f'PV_FN_SLICE_f{n}'
 sig='''(resources : Resources) (encode : Encode) (base : Carrier OWNER Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a bytes : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)'''
 args='resources encode base K s parents a bytes w prior external backend'
 s=f'''import PV_LIB_Observation
import {root}
set_option autoImplicit false
noncomputable section
namespace {ns}
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open {root}

def result {sig} :=
  outcome s parents a (PV_STX2_Source7AllocationRuntimeEntry.layout bytes 4) prior
    (reply resources encode base K s parents a bytes w external backend)

def actual {sig} :=
  advance (PV_STX2_Source7CapacityScalars.carrier base) K (fun _ => none)
    (handler resources encode base K s parents a bytes external backend)
    (result {args}).1 (start s parents a w prior)

def model {sig} (stack : List Config) :=
  PV_LIB.observe (⟨(result {args}).2,stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)

def law {sig} (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model {args} stack

theorem certified {sig} (stack : List Config)
    (pre : Pre s parents a bytes w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources) :
    law {args} stack
      (PV_LIB.observe (⟨actual {args},stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) ∧
    Post {args} := by
  have h := contract {args} pre malloc_semantics calloc_semantics
  refine ⟨?_,h⟩
  change PV_LIB.observe (⟨actual {args},stack⟩ : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) = _
  unfold actual result
  rw [h.1]
#print axioms certified
end {ns}
'''
 Path('lean',ns+'.lean').write_text(s)

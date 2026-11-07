import NMB_Input
set_option autoImplicit false
noncomputable section
namespace NMB_Heap
open Aeneas Aeneas.Std Result AspisR1 S2Trust
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint
/-- Full runtime heap, with original per-occurrence descriptors as ambient
state. No account record is reindexed by the data cell. -/
def payload (x : NMB_Input.Input) (c : Nat) : Payload :=
 {(source (nativeBytes (x.buffers c))) with
  descriptor:=⟨x.base c,(x.buffers c).val.length,x.provenance c⟩}
def heap (x : NMB_Input.Input) : Heap (Nat → NMB_Input.Owned) :=
 {accounts:=x.handles,ownerLive:=fun _=>true,allocated:=fun _=>true,
  payload:=payload x,counter:=fun _=>0,external:=fun _=>0,guards:=[],ambient:=x.descriptors}
theorem bytes (x : NMB_Input.Input) (i : Nat) :
 NLF_RuntimeInterpretation.byteList (heap x) i=nativeBytes (x.buffers i) := by
 apply List.ext_getElem
 · simp [NLF_RuntimeInterpretation.byteList,heap,payload,nativeBytes]
 · intro j hj hk
   simp [NLF_RuntimeInterpretation.byteList,heap,payload,source,List.getElem?_eq_getElem hk]
theorem installation (x : NMB_Input.Input) :
 (NLF_RuntimeInterpretation.install (heap x) x.records x.money).state=x.sdk := by
 change NLF_SdkModel.State.mk _ _=NLF_SdkModel.State.mk _ _
 congr 1
 funext i
 congr 2
 exact bytes x i
#print installation
#print axioms bytes
#print axioms installation
end NMB_Heap

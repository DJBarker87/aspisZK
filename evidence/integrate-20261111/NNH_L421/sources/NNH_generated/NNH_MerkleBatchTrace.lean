import NNH_MerkleBatchExecute
import NNC_C04Events
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleBatchTrace
open Aeneas Aeneas.Std NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def calls (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → Indices → Values → SdkC_Source.Log
 | [],_,_ => []
 | (root,kind)::rest,idx,val =>
   let head := NNH_MerkleTreeExecute.run H proof raw root batch kind idx val
   match head.2 with
   | (.Err _,_,_) => NNC_C04Events.tree kind head.1
   | (.Ok (),nextIdx,nextVal) =>
     NNC_C04Events.tree kind head.1 ++ calls H proof raw batch rest nextIdx nextVal

theorem native (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (batch : Usize) (sites : List Call) (idx : Indices) (val : Values) :
 NNC_C04Events.Returned H proof raw batch sites idx val
  (NNH_MerkleBatchExecute.calls H proof raw batch sites idx val).1
  (NNH_MerkleBatchExecute.calls H proof raw batch sites idx val).2
  (calls H proof raw batch sites idx val) := by
 induction sites generalizing idx val with
 | nil => exact .nil idx val
 | cons head rest ih =>
   rcases head with ⟨root,kind⟩
   have child := NNH_MerkleTreeExecute.native H proof raw root batch kind idx val
   cases answer : (NNH_MerkleTreeExecute.run H proof raw root batch kind idx val).2 with
   | mk reply state =>
    rcases state with ⟨nextIdx,nextVal⟩
    cases reply with
    | Err error =>
      rw [answer] at child
      simp only [calls,NNH_MerkleBatchExecute.calls,answer]
      exact .error root kind rest idx nextIdx val nextVal _ error child
    | Ok result =>
      cases result
      rw [answer] at child
      simp only [calls,NNH_MerkleBatchExecute.calls,answer]
      exact .next root kind rest idx nextIdx val nextVal _ _ _ _ child (ih nextIdx nextVal)

#print axioms native
end AspisR1.NNH_MerkleBatchTrace

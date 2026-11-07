import NNH_MerkleTreeExecute
import NLL_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleBatchExecute
open Aeneas Aeneas.Std NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def calls (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → Indices → Values → History × Reply
 | [],_,_ => ([],.Ok ())
 | (root,kind)::rest,idx,val =>
   let head := NNH_MerkleTreeExecute.run H proof raw root batch kind idx val
   match head.2 with
   | (.Err error,_,_) => (leafHistory kind head.1,.Err error)
   | (.Ok (),nextIdx,nextVal) =>
     let tail := calls H proof raw batch rest nextIdx nextVal
     (leafHistory kind head.1++tail.1,tail.2)

theorem calls_native (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (batch : Usize) (sites : List Call) (idx : Indices) (val : Values) :
 Calls H proof raw batch sites idx val (calls H proof raw batch sites idx val).1
  (calls H proof raw batch sites idx val).2 := by
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
      simp only [calls,answer]
      exact .error root kind rest idx nextIdx val nextVal _ error child
    | Ok unit =>
      cases unit
      rw [answer] at child
      simp only [calls,answer]
      exact .next root kind rest idx nextIdx val nextVal _ _ _ child (ih nextIdx nextVal)

def run (H : Bytes → State) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
 (folded : Root) (batch : Usize) : History × Reply :=
 calls H proof p.queries batch (sites (NLL_BatchSource.roots p folded))
  NKV_ParentSource.zeroI NKV_ParentSource.zeroV

theorem native (H : Bytes → State) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
 (folded : Root) (batch : Usize) :
 NLL_BatchSource.Invocation H proof p folded batch (run H proof p folded batch).1
  (run H proof p folded batch).2 :=
 calls_native H proof p.queries batch _ _ _
#print axioms calls_native
#print axioms native
end AspisR1.NNH_MerkleBatchExecute

import NNH_MerkleLoopExecute
import NLL_ParentInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleTreeExecute
open Aeneas Aeneas.Std NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def initial (H : Bytes → State) (raw : Array U32 22#usize) (batch kind : Usize)
 (idx : Indices) (val : Values) : Frame :=
 ⟨entryKeys H raw batch.val kind,NJV_EntryABI.initial idx val 0#usize,0#usize⟩

def run (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Root) (batch kind : Usize) (idx : Indices) (val : Values) : List Event × Answer :=
 let tail := NNH_MerkleLoopExecute.run H proof root batch.val kind (NKB_KeyStream.lo batch.val)
  (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)
  (NKB_KeyStream.count batch.val).val (initial H raw batch kind idx val)
 (.entry (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
  (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)
  (entryKeys H raw batch.val kind)::tail.1,tail.2)

theorem native (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Root) (batch kind : Usize) (idx : Indices) (val : Values) :
 Invocation H proof raw root batch kind idx val (run H proof raw root batch kind idx val).1
  (run H proof raw root batch kind idx val).2 := by
 refine ⟨_,rfl,?_⟩
 have bound := (NKB_KeyStream.positive batch.val).2
 exact NNH_MerkleLoopExecute.native H proof root batch.val kind (NKB_KeyStream.lo batch.val)
  (NKB_KeyStream.count batch.val) _ (by omega) _ _ rfl (by change 0+_ ≤ 16; omega)
#print axioms native
end AspisR1.NNH_MerkleTreeExecute

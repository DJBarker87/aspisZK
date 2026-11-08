import NNY_BatchArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleTreeFrame
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchBody NKV_StepErasure NKV_LoopTransport
def code (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (idx : Indices) (val : Values) := do
 let a ← base.op4 queries lo n tree
 let keys ← base.op5 a n
 let (idx1,val1,pending) ← verifier.candidate.batch_tree_loop (Port3_BatchStd.install base)
  D proof root tree idx val () lo n slot keys 0#usize 0#usize
 match pending with
 | none => fail .panic
 | some r => ok (r,idx1,val1)
theorem head (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (batch tree lo hi n slot : Usize) (idx : Indices) (val : Values)
 (branch : (if batch=0#usize then do let i ← (Port3_BatchStd.install base).op13; ok (0#usize,i)
            else do let i ← (Port3_BatchStd.install base).op13; ok (i,22#usize))=ok (lo,hi))
 (delta : Usize.wrapping_sub hi lo=n)
 (slotEq : Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) tree=slot) :
 verifier.candidate.batch_tree (Port3_BatchStd.install base) D proof queries root batch tree idx val () =
 code base D proof queries root tree lo n slot idx val := by
 unfold verifier.candidate.batch_tree
 rw [branch]
 change (do
  let a ← base.op4 queries lo (Usize.wrapping_sub hi lo) tree
  let keys ← base.op5 a (Usize.wrapping_sub hi lo)
  let (idx1,val1,pending) ← verifier.candidate.batch_tree_loop (Port3_BatchStd.install base)
   D proof root tree idx val () lo (Usize.wrapping_sub hi lo)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) tree) keys 0#usize 0#usize
  match pending with | none => fail .panic | some r => ok (r,idx1,val1)) = _
 rw [delta,slotEq]
 rfl

theorem zero (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree : Usize) (idx : Indices) (val : Values) :
 verifier.candidate.batch_tree (Port3_BatchStd.install base) D proof queries root 0#usize tree idx val () =
 code base D proof queries root tree 0#usize 10#usize
  (Usize.wrapping_add 0#usize tree) idx val :=
 head base D proof queries root 0#usize tree 0#usize 10#usize 10#usize _ idx val
  (by rw [if_pos rfl]; rfl) (NNY_BatchArithmetic.sub_zero _)
  (by rw [NNY_BatchArithmetic.mul_zero])

theorem one (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree : Usize) (idx : Indices) (val : Values) :
 verifier.candidate.batch_tree (Port3_BatchStd.install base) D proof queries root 1#usize tree idx val () =
 code base D proof queries root tree 10#usize 12#usize
  (Usize.wrapping_add 3#usize tree) idx val :=
 head base D proof queries root 1#usize tree 10#usize 22#usize 12#usize _ idx val
  (by rw [if_neg (show ¬1#usize=0#usize from by decide)]; rfl) NNY_BatchArithmetic.sub_twelve
  (by rw [NNY_BatchArithmetic.mul_one])
#print axioms head
#print axioms zero
#print axioms one
end AspisR1.NNY_MerkleTreeFrame
end

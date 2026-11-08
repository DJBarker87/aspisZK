import NNU_MerkleChildren
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
theorem zero (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree : Usize) (idx : Indices) (val : Values) :
 verifier.candidate.batch_tree (Port3_BatchStd.install base) D proof queries root 0#usize tree idx val () =
 code base D proof queries root tree 0#usize 10#usize
  (Usize.wrapping_add 0#usize tree) idx val := by
 unfold verifier.candidate.batch_tree code
 simp only [Port3_BatchStd.install,if_pos (show 0#usize=0#usize from rfl),bind_tc_ok,lift]
 all_goals rfl
theorem one (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree : Usize) (idx : Indices) (val : Values) :
 verifier.candidate.batch_tree (Port3_BatchStd.install base) D proof queries root 1#usize tree idx val () =
 code base D proof queries root tree 10#usize 12#usize
  (Usize.wrapping_add 3#usize tree) idx val := by
 unfold verifier.candidate.batch_tree code
 simp only [Port3_BatchStd.install,if_neg (show ¬1#usize=0#usize from by decide),bind_tc_ok,lift]
 all_goals rfl
#print axioms zero
#print axioms one
end AspisR1.NNY_MerkleTreeFrame
end

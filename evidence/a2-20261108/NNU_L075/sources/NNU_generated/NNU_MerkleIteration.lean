import NNU_MerkleChildren
import Port4B_NativeLeaf
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleIteration
open Aeneas Aeneas.Std Result MultiproofConeRef
open Port4B_NativeLeaf

theorem source (env : RSL.Env) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot pos : Usize) (keys : Array U64 16#usize) (s : reference.Scratch)
 (key : U64) (view : Slice U8) (leaf : Array U8 32#usize)
 (more : pos < n) (room : s.n.val < 16)
 (keyRead : Array.index_usize keys pos=.ok key)
 (viewRead : (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op2 proof (openingIndex lo key)=.ok view)
 (width : view.val.length=832)
 (leafRead : (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op6
   (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) () tree view=.ok leaf) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
   (Port3_BatchStd.install (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)))
   (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) proof root tree () lo n slot keys s.idx s.val s.n pos=
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
   (Port3_BatchStd.install Port4B_Install.leaves)
   (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) proof root tree () lo n slot keys s.idx s.val s.n pos := by
 have targetView : Port4B_Install.leaves.op2 proof (openingIndex lo key)=.ok view := by
   change Port4B_Opening.opening proof (openingIndex lo key)=.ok view
   rw [←NNU_MerkleChildren.opening]
   exact viewRead
 have targetLeaf : Port4B_Install.leaves.op6 (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) () tree view=.ok leaf := by
   change Port4B_LeafCode.native (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) () tree view=.ok leaf
   rw [←NNU_MerkleChildren.leaf env tree view width]
   exact leafRead
 have left := Port4B_NativeLeaf.step (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env))
   (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) () proof root tree lo n slot pos keys s
   key view leaf more room keyRead viewRead leafRead
 have right := Port4B_NativeLeaf.step Port4B_Install.leaves
   (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) () proof root tree lo n slot pos keys s
   key view leaf more room keyRead targetView targetLeaf
 exact left.trans right.symm
#print axioms source
end AspisR1.NNU_MerkleIteration
end

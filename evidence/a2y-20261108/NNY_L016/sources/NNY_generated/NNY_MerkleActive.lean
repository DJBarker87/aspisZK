import NNY_MerkleAgreement
import NNY_OpeningWidth
import NNU_MerkleChildren
import Port4B_NativeLeaf
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport
/-- One arbitrary active native iteration. The checked opening proves the
leaf domain; the post-hash mutation is literally shared. No scratch invariant
or whole-loop equality is assumed. -/
theorem active (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d pos : Usize) (keys : Array U64 16#usize)
 (idx : Indices) (val : Values) (more : pos < n) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
  proof root tree () lo n slot keys idx val d pos =
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install Port4B_Install.leaves) (VTop_Checkpoint.digest D)
  proof root tree () lo n slot keys idx val d pos := by
 rw [Port4B_NativeLeaf.active _ _ () proof root tree lo n slot d pos keys idx val more,
  Port4B_NativeLeaf.active _ _ () proof root tree lo n slot d pos keys idx val more]
 cases keyRead : Array.index_usize keys pos with
 | fail e => simp only [keyRead,bind_tc_fail]
 | div => simp only [keyRead,bind_tc_div]
 | ok key =>
   simp only [keyRead,bind_tc_ok]
   have opening : (NKV_ConcreteChildren.ops H).op2 proof (Port4B_NativeLeaf.openingIndex lo key)=
    Port4B_Install.leaves.op2 proof (Port4B_NativeLeaf.openingIndex lo key) :=
    NNU_MerkleChildren.opening proof _
   rw [opening]
   cases viewRead : Port4B_Install.leaves.op2 proof (Port4B_NativeLeaf.openingIndex lo key) with
   | fail e => simp only [viewRead,bind_tc_fail]
   | div => simp only [viewRead,bind_tc_div]
   | ok view =>
     simp only [viewRead,bind_tc_ok]
     have width := NNY_OpeningWidth.source proof view _ viewRead
     have left := NKV_ConcreteDomains.leaf H (NKV_ConcreteChildren.digest H) () tree view width
     have right := leaf D H agree tree view width
     change (do let l ← (NKV_ConcreteChildren.ops H).op6 (NKV_ConcreteChildren.digest H) () tree view
                Port4B_LeafStep.post idx val d (Port4B_NativeLeaf.decodedIndex key) l (Usize.wrapping_add pos 1#usize)) =
      (do let l ← Port4B_LeafCode.native (VTop_Checkpoint.digest D) () tree view
          Port4B_LeafStep.post idx val d (Port4B_NativeLeaf.decodedIndex key) l (Usize.wrapping_add pos 1#usize))
     rw [left,right]
#print axioms active
end AspisR1.NNY_MerkleShared
end

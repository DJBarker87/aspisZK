import NNY_MerkleTerminalBuild
import NNY_MerkleVerify
import NNU_MerkleCount
import NNU_MerkleChildren
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport

theorem terminal (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d : Usize) (keys : Array U64 16#usize)
 (idx outIdx : Indices) (val outVal : Values) (slotBound : slot.val < 6)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H))
  (NKV_ConcreteChildren.digest H) proof root tree () lo n slot keys idx val d n=
  .ok (.done (outIdx,outVal,some (.Ok ())))) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof root tree () lo n slot keys idx val d n=
  .ok (.done (outIdx,outVal,some (.Ok ()))) := by
 obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,
   capRead,fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=
   Port4B_TailReads.reads (NKV_ConcreteChildren.ops H)
    (NKV_ConcreteChildren.digest H) () proof root tree lo n slot d
    keys idx outIdx val outVal run
 have targetCount : Port4B_Install.leaves.op11 .Two front=.ok (some count) := by
   change Port4B_CountInstall.nodeCount .Two front=.ok (some count)
   rw [←NNU_MerkleCount.source]
   exact countRead
 have targetNode : Port4B_Install.leaves.op3 proof slot=.ok nodes := by
   change Port4B_SlotInstall.nodeSlot proof slot=.ok nodes
   rw [←NNU_MerkleChildren.slot proof slot slotBound]
   exact nodeRead
 have targetVerify : Port4B_Install.leaves.op10 (VTop_Checkpoint.digest D) ()
   .Two root idx val d supplied=.ok (true,outIdx,outVal) :=
   verify D H agree root idx outIdx val outVal d supplied verifyRead
 have callback := NNY_MerkleTerminalFrame.callback
   (NKV_ConcreteChildren.ops H) Port4B_Install.leaves
   (NKV_ConcreteChildren.digest H)
   (VTop_Checkpoint.digest D)
 rw [callback] at scanRead
 rw [NNY_MerkleTerminalFrame.source Port4B_Install.leaves _ proof root () tree lo n slot d n keys idx val (by simp)]
 exact NNY_MerkleTerminalBuild.constructed Port4B_Install.leaves _ proof root slot d idx outIdx val outVal
  front count cap nodes padding supplied ce after frontRead targetCount targetNode capRead fit
  paddingRead chunksRead scanRead prefixRead targetVerify
#print axioms terminal
end AspisR1.NNY_MerkleShared
end

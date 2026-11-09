import NOM_MerkleVerify
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOM_MerkleLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport

/-- Converse of NOC_MerkleBounded.terminal: every tail read is an equality
except verify, which is NOM_MerkleVerify.verify. -/
theorem terminal (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NOC_MerkleBounded.NodeLeaf D H)
 (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d : Usize) (keys : Array U64 16#usize)
 (idx outIdx : Indices) (val outVal : Values) (slotBound : slot.val < 6)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof root tree () lo n slot keys idx val d n=
  .ok (.done (outIdx,outVal,some (.Ok ())))) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H))
  (NKV_ConcreteChildren.digest H) proof root tree () lo n slot keys idx val d n=
  .ok (.done (outIdx,outVal,some (.Ok ()))) := by
 obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,
   capRead,fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=
   Port4B_TailReads.reads Port4B_Install.leaves (VTop_Checkpoint.digest D) () proof root tree
    lo n slot d keys idx outIdx val outVal run
 have targetCount : (NKV_ConcreteChildren.ops H).op11 .Two front=.ok (some count) :=
   (NNU_MerkleCount.source front).trans countRead
 have targetNode : (NKV_ConcreteChildren.ops H).op3 proof slot=.ok nodes :=
   (NNU_MerkleChildren.slot proof slot slotBound).trans nodeRead
 have targetVerify : (NKV_ConcreteChildren.ops H).op10 (NKV_ConcreteChildren.digest H) ()
   .Two root idx val d supplied=.ok (true,outIdx,outVal) :=
   NOM_MerkleVerify.verify D H agree root idx outIdx val outVal d supplied verifyRead
 have callback := NNY_MerkleTerminalFrame.callback
   Port4B_Install.leaves (NKV_ConcreteChildren.ops H)
   (VTop_Checkpoint.digest D) (NKV_ConcreteChildren.digest H)
 rw [callback] at scanRead
 rw [NNY_MerkleTerminalFrame.source (NKV_ConcreteChildren.ops H) _ proof root () tree lo n slot d n keys idx val (by simp)]
 exact NNY_MerkleTerminalBuild.constructed (NKV_ConcreteChildren.ops H) _ proof root slot d idx outIdx val outVal
  front count cap nodes padding supplied ce after frontRead targetCount targetNode capRead fit
  paddingRead chunksRead scanRead prefixRead targetVerify

/-- Converse of NOC_MerkleBounded.loop: least-fixed-point transport with the
roles of the two dictionaries exchanged; active is an equality, the terminal
step is the converse above. -/
theorem loop (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NOC_MerkleBounded.NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d pos : Usize) (keys : Array U64 16#usize)
 (idx outIdx : Indices) (val outVal : Values) (slotBound : slot.val<6)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
  (Port3_BatchStd.install Port4B_Install.leaves) (VTop_Checkpoint.digest D)
  proof root tree idx val () lo n slot keys d pos = ok (outIdx,outVal,some (.Ok ()))) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
  proof root tree idx val () lo n slot keys d pos = ok (outIdx,outVal,some (.Ok ())) := by
 unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop at run ⊢
 refine NNY_LoopTransport.accepted _ _ (fun out : CohortOut => out.2.2=some (.Ok ()))
  ?_ (idx,val,d,pos) (outIdx,outVal,some (.Ok ())) rfl run
 rintro ⟨i,v,count,cursor⟩ result read
 by_cases more : cursor<n
 · have same := NOC_MerkleBounded.active D H agree proof root tree lo n slot count cursor keys i v more
   cases result <;> simp only <;> (try intro)
   all_goals exact same.trans read
 · have src := NNY_MerkleTerminalFrame.source Port4B_Install.leaves
    (VTop_Checkpoint.digest D) proof root () tree lo n slot count cursor keys i v more
   cases result with
   | cont next =>
     exact False.elim (NNY_TerminalControl.no_cont _ _ proof root slot count i v next (src.symm.trans read))
   | done output =>
     rcases output with ⟨oi,ov,pending⟩
     intro good
     change pending=some (.Ok ()) at good
     subst pending
     have atEnd : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (VTop_Checkpoint.digest D)
      proof root tree () lo n slot keys i v count n=ok (.done (oi,ov,some (.Ok ()))) := by
       rw [NNY_MerkleTerminalFrame.source _ _ proof root () tree lo n slot count n keys i v (by simp)]
       exact src.symm.trans read
     have target := terminal D H agree proof root tree lo n slot count keys i oi v ov slotBound atEnd
     have dst := NNY_MerkleTerminalFrame.source (NKV_ConcreteChildren.ops H)
      (NKV_ConcreteChildren.digest H) proof root () tree lo n slot count cursor keys i v more
     have dstEnd := NNY_MerkleTerminalFrame.source (NKV_ConcreteChildren.ops H)
      (NKV_ConcreteChildren.digest H) proof root () tree lo n slot count n keys i v (by simp)
     exact dst.trans (dstEnd.symm.trans target)

#print axioms terminal
#print axioms loop
end AspisR1.NOM_MerkleLoop
end

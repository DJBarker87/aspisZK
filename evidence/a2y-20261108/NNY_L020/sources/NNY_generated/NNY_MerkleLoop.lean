import NNY_LoopTransport
import NNY_MerkleActive
import NNY_MerkleTerminal
import NNY_TerminalControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport
/-- Accepted-loop transport uses the single native iteration on arbitrary
scratch. Its invariant is True: checked opening reads establish width locally,
and the unchanged post-hash mutation preserves all continued source states. -/
theorem loop (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d pos : Usize) (keys : Array U64 16#usize)
 (idx outIdx : Indices) (val outVal : Values) (slotBound : slot.val<6)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
  proof root tree idx val () lo n slot keys d pos = ok (outIdx,outVal,some (.Ok ()))) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
  (Port3_BatchStd.install Port4B_Install.leaves) (VTop_Checkpoint.digest D)
  proof root tree idx val () lo n slot keys d pos = ok (outIdx,outVal,some (.Ok ())) := by
 unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop at run ⊢
 apply NNY_LoopTransport.accepted _ _ (fun out => out.2.2=some (.Ok ())) _ _ rfl run
 rintro ⟨i,v,count,cursor⟩ result read
 by_cases more : cursor<n
 · have same := active D H agree proof root tree lo n slot count cursor keys i v more
   cases result <;> simp only <;> (try intro)
   all_goals exact same.symm.trans read
 · have src := NNY_MerkleTerminalFrame.source (NKV_ConcreteChildren.ops H)
    (NKV_ConcreteChildren.digest H) proof root () tree lo n slot count cursor keys i v more
   cases result with
   | cont next =>
     exact False.elim (NNY_TerminalControl.no_cont _ _ proof root slot count i v next (src.symm.trans read))
   | done output =>
     rcases output with ⟨oi,ov,pending⟩
     intro good
     change pending=some (.Ok ()) at good
     subst pending
     have atEnd : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
      proof root tree () lo n slot keys i v count n=ok (.done (oi,ov,some (.Ok ()))) := by
       rw [NNY_MerkleTerminalFrame.source _ _ proof root () tree lo n slot count n keys i v (by simp)]
       exact src.symm.trans read
     have target := terminal D H agree proof root tree lo n slot count keys i oi v ov slotBound atEnd
     rw [NNY_MerkleTerminalFrame.source _ _ proof root () tree lo n slot count cursor keys i v more,
      ←NNY_MerkleTerminalFrame.source _ _ proof root () tree lo n slot count n keys i v (by simp)]
     exact target
#print axioms loop
end AspisR1.NNY_MerkleShared
end

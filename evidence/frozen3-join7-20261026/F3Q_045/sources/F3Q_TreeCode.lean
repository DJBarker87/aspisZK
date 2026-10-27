import F3Q_BatchValue
import Port9OR_BatchTree
import Port4B_TreeCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TreeCode
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem log {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (proof : Slice U8) (root : Array U8 32#usize) (queries : Array U32 22#usize)
    (batch kind : Usize) (idx outIdx : Indices) (val outVal : Values)
    (raw keys : Array U64 16#usize)
    (built : (Port9OR_BatchStep.ops Port4B_Install.leaves).op4 queries (Port4B_TreeCuts.lo batch)
      (Port4B_TreeCuts.count batch) kind=ok raw)
    (sorted : (Port9OR_BatchStep.ops Port4B_Install.leaves).op5 raw (Port4B_TreeCuts.count batch)=ok keys)
    (small : (Port4B_TreeCuts.count batch).val<256)
    (loop : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop Port4B_Install.leaves D proof root kind
      idx val hash (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind)
      keys 0#usize 0#usize=ok (outIdx,outVal,some (.Ok ()))) :
    (eval H (SdkC_Oracle.program (Port9OR_BatchTree.code Port4B_Install.leaves D hash proof queries root batch kind idx val))).1=
      (eval H (SdkC_Oracle.program (Port9OR_BatchLoop.code Port4B_Install.leaves D hash proof root kind
        (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind)
        keys ((Port4B_TreeCuts.count batch).val+1) idx val 0#usize 0#usize))).1 := by
  have value := F3Q_IdealCode.value D hash H law (Port9OR_BatchLoop.code Port4B_Install.leaves D hash proof root kind
    (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind)
    keys ((Port4B_TreeCuts.count batch).val+1) idx val 0#usize 0#usize)
  rw [Port9OR_BatchLoop.source Port4B_Install.leaves D D hash proof root kind _ _ _ keys small] at value
  · rw [loop] at value
    unfold Port9OR_BatchTree.code
    simp only [Bind.bind,CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,built,sorted,
      SdkC_Oracle.program]
    simp only [F3Q_CodeEval.bind_eval,value,Pure.pure,CheckpointBytes5Effect.liftResult,
      SdkC_Oracle.program,eval,List.append_nil]
  · simp

#print axioms log
end AspisR1.F3Q_TreeCode
end

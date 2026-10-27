import F3Q_TreeValue
import F3Q_CodeEval
import Port9OR_Batch
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_BatchCodeLog
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem compose {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (batch : Usize)
    (idx1 idx2 idx3 : Indices) (val1 val2 val3 : Values)
    (c0 : Port3_NativeBatchBody.verifier.candidate.batch_tree Port4B_Install.leaves D proof p.queries
      (Port3_BatchStage.root0 p) batch 0#usize (Array.repeat 16#usize 0#u32)
      (Array.repeat 16#usize (Array.repeat 32#usize 0#u8)) hash=ok (.Ok (),idx1,val1))
    (c1 : Port3_NativeBatchBody.verifier.candidate.batch_tree Port4B_Install.leaves D proof p.queries
      (Port3_BatchStage.root1 p) batch 1#usize idx1 val1 hash=ok (.Ok (),idx2,val2))
    (c2 : Port3_NativeBatchBody.verifier.candidate.batch_tree Port4B_Install.leaves D proof p.queries
      folded batch 2#usize idx2 val2 hash=ok (.Ok (),idx3,val3)) :
    (eval H (SdkC_Oracle.program (Port9OR_Batch.code Port4B_Install.leaves D hash proof p folded batch))).1=
      (eval H (SdkC_Oracle.program (Port9OR_BatchTree.code Port4B_Install.leaves D hash proof p.queries
        (Port3_BatchStage.root0 p) batch 0#usize (Array.repeat 16#usize 0#u32)
        (Array.repeat 16#usize (Array.repeat 32#usize 0#u8))))).1 ++
      (eval H (SdkC_Oracle.program (Port9OR_BatchTree.code Port4B_Install.leaves D hash proof p.queries
        (Port3_BatchStage.root1 p) batch 1#usize idx1 val1))).1 ++
      (eval H (SdkC_Oracle.program (Port9OR_BatchTree.code Port4B_Install.leaves D hash proof p.queries
        folded batch 2#usize idx2 val2))).1 := by
  have h0 : Array.index_usize p.roots 0#usize=ok (Port3_BatchStage.root0 p) := by simp [Array.index_usize,Port3_BatchStage.root0]
  have h1 : Array.index_usize p.roots 1#usize=ok (Port3_BatchStage.root1 p) := by simp [Array.index_usize,Port3_BatchStage.root1]
  have v0 := (F3Q_TreeValue.value D hash H law proof p.queries (Port3_BatchStage.root0 p) batch 0#usize
    (Array.repeat 16#usize 0#u32) (Array.repeat 16#usize (Array.repeat 32#usize 0#u8))).trans c0
  have v1 := (F3Q_TreeValue.value D hash H law proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx1 val1).trans c1
  have v2 := (F3Q_TreeValue.value D hash H law proof p.queries folded batch 2#usize idx2 val2).trans c2
  unfold Port9OR_Batch.code
  simp only [Bind.bind,CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,h0,h1,SdkC_Oracle.program]
  have zero : (0#usize).val=0 := by scalar_tac
  have one : (1#usize).val=1 := by scalar_tac
  have two : (2#usize).val=2 := by scalar_tac
  unfold Port9OR_Batch.values
  simp only [Array.index_usize,Array.getElem?_Usize_eq,Array.make,zero,one,two,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Bind.bind,CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,SdkC_Oracle.program]
  simp only [F3Q_CodeEval.bind_eval,v0,v1,v2,
    core.result.Result.Insts.CoreOpsTry.branch,Bind.bind,CheckpointBytes5Effect.bind,
    CheckpointBytes5Effect.liftResult,Pure.pure,SdkC_Oracle.program,eval,List.append_nil,List.append_assoc]

#print axioms compose
end AspisR1.F3Q_BatchCodeLog
end

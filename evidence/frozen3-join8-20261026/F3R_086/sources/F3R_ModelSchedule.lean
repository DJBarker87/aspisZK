import F3_Checkpoint
import F3K_SamplerProtocol
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_ModelSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
attribute [local instance] Classical.propDecidable

theorem complete (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (p : Parsed) (q : Fin 22 → Fin 262144) (input : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View)
    (guard : OraclePortAdmission.Guard (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2))
    (parser : OraclePortStoredParserC4.parseReached i.stored (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p)
    (queries : OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some q)
    (found : OraclePortStoredDecisionDraftC4.input p q (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some input)
    (opening : LiteralOpeningView.read (typedRows p q (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2))=some v)
    (batch0 : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true)
    (batch1 : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).2=true)
    (finish : OraclePortFrozen2.finish p q (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) input
      (OraclePortFrozen2.completeState input q)=true) :
    eval H (F3_Model.verifier D i)=
      ((eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ++
        ((eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
        ((eval H (F3_Model.checkpoint i.physical i.stored p q (LiteralTranscript.erasePrefix
          (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) input v)).1 ++
          (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1)),true) := by
  have sampler := F3K_SamplerProtocol.initial D H i.semantic.value i.proof 33
  have logEq := congrArg Prod.fst sampler
  have trEq := congrArg Prod.snd sampler
  rw [F3_Model.complete_schedule,←logEq,←trEq]
  simp only [OracleDecisionFeasibilityCore.onBytes,F3_Model.decision,if_pos guard,parser,queries,
    eval_bind,batch0,if_true,F3_Model.afterBatch0,found,opening,F3_Model.checkpoint_value,
    OraclePortFrozen2.stage2,eval_bind,batch1,if_true,eval,finish,List.append_nil,List.append_assoc]

#print axioms complete
end AspisR1.F3R_ModelSchedule
end

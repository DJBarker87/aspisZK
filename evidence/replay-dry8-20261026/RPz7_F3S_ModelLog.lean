import RPz7_F3R_ModelSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_ModelLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
 theorem schedule (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
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
    (batch0 : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true) :
    (eval H (F3_Model.verifier D i)).1=
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ++
      ((eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
       ((eval H (F3_Model.checkpoint i.physical i.stored p q (LiteralTranscript.erasePrefix
          (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) input v)).1 ++
        (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1)) := by
  have sampler := F3K_SamplerProtocol.initial D H i.semantic.value i.proof 33
  have logEq := congrArg Prod.fst sampler
  have trEq := congrArg Prod.snd sampler
  dsimp only at logEq trEq
  rw [F3_Model.complete_schedule]
  dsimp only
  rw [←logEq,←trEq]
  change _ ++ (eval H (F3_Model.decision i.physical i.stored _ _)).1 = _
  rw [F3_Checkpoint.terminal_schedule H i.physical i.stored _ _ p q input v guard parser queries found opening batch0]
  simp only [List.append_assoc]
#print axioms schedule
end AspisR1.F3S_ModelLog
end

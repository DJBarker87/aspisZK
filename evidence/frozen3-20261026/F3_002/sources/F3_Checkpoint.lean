import F3_Model
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3_Checkpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5 OraclePortCheckpointOracleC5

/-- Six ordered issued reads, including duplicate S/P/checksum reads.
The checksum authenticates the SAME writer body on resume. -/
theorem schedule (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (c : Context) (d : MatchingSupport.Data E)
    (rho : K) (q : Fin 22 → Fin 262144) :
    let p := prepared c d rho q
    let a := (OraclePortCheckpointStateC3.write (model d rho q)).accumulator
    let addr := OraclePortPhysicalFrameDraft.domain ++ body p a (H stored) (H physical.bytes)
    (eval H (writeResume stored physical.bytes c d rho q)).1 =
      [(stored,H stored),(physical.bytes,H physical.bytes),(addr,H addr),
       (stored,H stored),(physical.bytes,H physical.bytes),(addr,H addr)] := by
  dsimp only
  have bound := (checksum_bound H stored physical.bytes (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator).1
  simp only [writeResume,eval_bind,writer_value]
  change _ = _
  simp only [writer,resumer,eval,List.append_nil]
  rw [bound]
  rfl

/-- The accepted terminal schedule is batch0, write/read checkpoint, batch1;
finish is pure. All three logs keep their chronological order. -/
theorem terminal_schedule (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View)
    (guard : OraclePortAdmission.Guard tr)
    (parsed : OraclePortStoredParserC4.parseReached stored tr = some p)
    (query : OraclePortSelectedDraft.queries tr = some q)
    (input : OraclePortStoredDecisionDraftC4.input p q tr = some i)
    (opening : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr) = some v)
    (first : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2 = true) :
    (eval H (F3_Model.decision physical stored tr m)).1 =
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
      (eval H (F3_Model.checkpoint physical stored p q tr i v)).1 ++
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1 := by
  simp only [F3_Model.decision,if_pos guard,parsed,query,eval_bind,first,if_true,
    F3_Model.afterBatch0,input,opening,F3_Model.checkpoint_value,
    OraclePortFrozen2.stage2,eval_bind,eval,List.append_nil,List.append_assoc]

#print axioms schedule
#print axioms terminal_schedule
end AspisR1.F3_Checkpoint
end

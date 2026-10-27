import RPz8_F3V_ReadModel
import RPz8_F3S_ModelAcceptance
import RPz8_F3S_AcceptanceValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_ModelAcceptance
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem values {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) (prior : Program Bytes State Unit)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (decoder : LiteralByteProtocol.Decoder)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domain : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned) :
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
        (D2 c H) () e.pub e.proof e.saved.deref t ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c B s H e prior) p q ∨
        F3S_AcceptanceValues.Values c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
          H (F3V_Checkpoint.trace c B s H e prior) p q tr data decoder i) := by
  obtain ⟨i,p,q,data,v,physical,stored,parser,queries,found,opening,guard,prepare,saved⟩ :=
    F3V_Checkpoint.saved c B s H e prior owner ports canonical domain multiply one inverse
  have parserProof : OraclePortStoredParserC4.parseReached (bytesOf e.proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [←stored];exact parser
  have parsed := (OraclePortStoredParserC4.parsed _ _ _ parserProof).1
  obtain ⟨t,calls,aux,outcome⟩ := F3V_Finish.reached c B s H e prior p parsed ports canonical domain multiply one inverse
  refine ⟨i,p,q,data,t,physical,stored,parser,queries,found,calls,?_⟩
  rcases saved with bad | saved
  · exact Or.inl bad
  · right
    have savedSource := saved
    rw [stored,physical] at savedSource
    have s2 := F3V_ReadModel.variant c B s H e t calls p data v q savedSource
    have ⟨_,_,_,_,_,_,_,_,_,finishCall,_⟩ := calls
    have outcome' : F3R_Finish.Outcome c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
        e.proof e.saved H i.stored i.physical.bytes e.run.p p (F3V_Checkpoint.trace c B s H e prior) := by
      rw [stored,physical];exact outcome
    exact F3S_ModelAcceptance.accepted c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
      e.proof e.saved H i.stored i.physical.bytes e.run.p p (F3V_Checkpoint.trace c B s H e prior)
      s2 finishCall outcome' decoder i q _ data v rfl (OraclePortCompactDraft.parse_header _ _ parsed).2
      guard parser queries found opening
      (F3V_FirstBatchModel.accepted c B s H e p parsed data.data _ q prepare)
      (F3V_SecondBatchModel.accepted c B s H e p parsed data.data _ q prepare) prepare saved

#print axioms values
end AspisR1.F3V_ModelAcceptance
end

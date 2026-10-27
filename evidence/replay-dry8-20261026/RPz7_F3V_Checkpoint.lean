import RPz7_F3V_Ten
import RPz7_F3V_WriterModel
import RPz7_F3N_TenInput
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Checkpoint
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

def trace {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) (prior : Program Bytes State Unit) :=
  (eval H prior).1 ++ AuS1_Recovery.log
    (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std (D1 c H)
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero)

theorem saved {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) (prior : Program Bytes State Unit)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domain : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned) :
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (v : LiteralOpeningView.View),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v ∧
      OraclePortAdmission.Guard tr ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data.data q (SelectedChallengeMap.rhoOf data.rho) ∧
      (AuS1_Finish.Collision H (trace c B s H e prior) p q ∨
        e.saved=Tx2N_Reader.writer H i.stored i.physical.bytes
          (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p data v)
            data.data (SelectedChallengeMap.rhoOf data.rho) q)
          (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data.data
            (SelectedChallengeMap.rhoOf data.rho) q)).accumulator) := by
  obtain ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,log,guard⟩ := e.prepared
  have parserProof : OraclePortStoredParserC4.parseReached (bytesOf e.proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [←stored];exact parser
  have ten := F3V_Ten.outcome c B s H e prior p (OraclePortStoredParserC4.parsed _ _ _ parserProof).1
  have result := F3N_TenInput.same_input e.run H (trace c B s H e prior) p ten ports q
    (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data prepare parserProof found
    canonical domain multiply one inverse
  refine ⟨i,p,q,data,v,physical,stored,parser,queries,found,opening,guard,prepare,?_⟩
  rcases result with bad | good
  · exact Or.inl bad
  · right
    have writer := F3V_WriterModel.saved c B s H e owner ports out output
    rw [prepared,good.1,←stored,←physical] at writer
    exact writer

#print axioms saved
end AspisR1.F3V_Checkpoint
end

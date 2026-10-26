import F3V_Checkpoint
import PFin_WorldSchedule
import PFin_WorldPrepared
import PFin_WorldCheckpoint
import PFin_WorldBatches
import F3V_Ten
import F3N_TenInput
import F3S_ModelLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldJoin
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem log {F C : Type} (base : Configuration F C) (s : Submission) (H : Bytes → State)
    (e : Evidence (F3V_Install.configuration base) base.boundaries s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source (F3V_Install.configuration base) hashv (input (F3V_Install.configuration base) s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base (F3V_Install.configuration base).currentBase
        (F3V_Install.configuration base).reserved (F3V_Install.configuration base).query (F3V_Install.configuration base).geometry)
        (F3V_Install.configuration base).boundaries (F3V_Install.configuration base).std)
      (D1 (F3V_Install.configuration base) H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize () none=ok (.Ok e.saved))
    (prior : Program Bytes State Unit) (decoder : LiteralByteProtocol.Decoder)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (F3V_Install.configuration base).currentBase)
        (F3V_Install.configuration base).reserved (F3V_Install.configuration base).query
        (F3V_Install.configuration base).geometry (F3V_Install.configuration base).boundaries (F3V_Install.configuration base).std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives (F3V_Install.configuration base).query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives (F3V_Install.configuration base).geometry)
    (domain : Port5Q1_Domain.SessionADomain (F3V_Install.configuration base).geometry)
    (multiply : (F3V_Install.configuration base).geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : (F3V_Install.configuration base).geometry.op7=ok (1#u32))
    (inverse : (F3V_Install.configuration base).geometry.op11=Port4C_InverseExecution.inverse_owned) :
    let c := F3V_Install.configuration base
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (out : AspisR1PublicPreparation.verifier.Prepared)
      (v : LiteralOpeningView.View),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧ OraclePortSelectedDraft.queries tr=some q ∧
      OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data.data q (SelectedChallengeMap.rhoOf data.rho) ∧
      AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=e.run.p ∧
      LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v ∧
      F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p data v)
        data.data (SelectedChallengeMap.rhoOf data.rho) q ∧
      OraclePortAdmission.Guard tr ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
        ((eval H (F3T_Installed.source c hashv (input c s))).1=(eval H (F3_Model.verifier decoder i)).1 ∧
          e.saved=Tx2N_Reader.writer H i.stored i.physical.bytes
            (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p data v)
              data.data (SelectedChallengeMap.rhoOf data.rho) q)
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data.data
              (SelectedChallengeMap.rhoOf data.rho) q)).accumulator)) := by
  dsimp only
  let c := F3V_Install.configuration base
  obtain ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,prepLog,guard⟩ :=
    PFin_WorldPrepared.fields base s H e
  have reached := parser
  rw [stored] at reached
  have parsed := (OraclePortStoredParserC4.parsed _ _ _ reached).1
  have ten := F3V_Ten.outcome c base.boundaries s H e prior p parsed
  have result := F3N_TenInput.same_input e.run H (F3V_Checkpoint.trace c base.boundaries s H e prior) p ten ports q
    _ data prepare reached found canonical domain multiply one inverse
  refine ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,guard,?_⟩
  rcases result with bad | good
  · exact Or.inl bad
  · right
    obtain ⟨p2,a2,root,view,reader,range,copy,batch,schedule⟩ := PFin_WorldSchedule.log c base.boundaries s H e hashv accepted first
    have batch0 := PFin_WorldBatches.first c base.boundaries s H e p parsed data.data _ q prepare
    have batch1 := PFin_WorldBatches.second c base.boundaries s H e p parsed data.data _ q prepare p2 a2 root view reader range copy batch
    have ck := PFin_WorldCheckpoint.log c base.boundaries s H e owner ports out output p2 a2 reader p data v q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) prepared good.1
    have model := F3S_ModelLog.schedule decoder H i p q data v guard parser queries found opening batch0.2
    rw [physical,stored] at model
    rw [prepLog,batch0.1,batch1.1] at schedule
    have joined := congrArg (fun ckLog=>
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ++
      ((eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
      (ckLog ++ (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1))) ck
    refine ⟨schedule.trans ((by simpa only [List.append_assoc] using joined).trans model.symm),?_⟩
    have writer := F3V_WriterModel.saved c base.boundaries s H e owner ports out output
    rw [prepared,good.1,←stored,←physical] at writer
    exact writer

#print axioms log
end AspisR1.PFin_WorldJoin
end

import F3W_FirstLog
import F3W_SecondLog
import F3W_SecondBatch
import F3W_CheckpointLog
import F3V_Checkpoint
import F3V_CheckpointOracle
import F3V_Ten
import F3R_PreparationInstall
import F3S_CheckpointOnRun
import F3S_ModelLog
import AuS1_Observe
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_LogJoin
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem joined {F C : Type} (base : Configuration F C)
    (s : Submission) (H : Bytes → State)
    (e : Evidence (F3V_Install.configuration base) base.boundaries s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base base.currentBase base.reserved base.query base.geometry)
        (F3V_Install.configuration base).boundaries base.std)
      (D1 (F3V_Install.configuration base) H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize () none=ok (.Ok e.saved))
    (prior : Program Bytes State Unit) (decoder : LiteralByteProtocol.Decoder) :
    let c := F3V_Install.configuration base
    ∀ (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domain : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs) (out : AspisR1PublicPreparation.verifier.Prepared)
    (v : LiteralOpeningView.View),
    i.physical.bytes=bytesOf e.pub.val → i.stored=bytesOf e.proof.val →
    let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
    OraclePortStoredParserC4.parseReached i.stored tr=some p →
    OraclePortSelectedDraft.queries tr=some q → OraclePortStoredDecisionDraftC4.input p q tr=some data →
    Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data.data q (SelectedChallengeMap.rhoOf data.rho) →
    AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=e.run.p →
    LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v →
    F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data v) data.data (SelectedChallengeMap.rhoOf data.rho) q →
    AspisR1PublicPreparation.PreparedHashCode.observe
      (AspisR1PublicPreparation.PreparedHashCode.run (SdkD_PrepareSource.code
        (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
        (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero))).1=
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 →
    OraclePortAdmission.Guard tr →
    AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
      (eval H (F3T_Installed.source c hashv (input c s))).1=(eval H (F3_Model.verifier decoder i)).1 := by
  dsimp only
  let c := F3V_Install.configuration base
  intro owner ports canonical domain multiply one inverse i p q data out v physical stored
    parser queries found prepare output opening prepared preparationLog guard
  have parserProof : OraclePortStoredParserC4.parseReached (bytesOf e.proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [←stored];exact parser
  have parsed := (OraclePortStoredParserC4.parsed _ _ _ parserProof).1
  have ten := F3V_Ten.outcome c base.boundaries s H e prior p parsed
  rcases F3N_TenInput.same_input e.run H (F3V_Checkpoint.trace c base.boundaries s H e prior) p ten ports q
      _ data prepare parserProof found canonical domain multiply one inverse with bad | good
  · exact Or.inl bad
  · right
    obtain ⟨p2,a2,root2,view2,read2,range2,copy2,batch2,secondLog⟩ :=
      F3W_SecondLog.log c base.boundaries s H e hashv
    have firstBatch := F3W_FirstBatch.accepted c base.boundaries s H e p parsed data.data _ q prepare
    have secondBatch := F3W_SecondBatch.accepted c base.boundaries s H e p parsed data.data _ q prepare
      p2 a2 root2 view2 read2 range2 copy2 batch2
    rw [←F3V_DigestCompatibility.same c H] at read2
    obtain ⟨after,effects,modelCheckpoint⟩ := F3W_CheckpointLog.stage _ c.reserved c.query c.geometry (D1 c H) ()
      (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run owner ports
      out output p2 a2 read2 H (by exact F3V_CheckpointOracle.oracle c H) p data v q _ prepared good.1
    obtain ⟨fields,size,can⟩ := WAdm_Inventory.on_run _ c.reserved c.query c.geometry (D1 c H) ()
      (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run owner ports
    have savedSize : 32≤e.saved.val.length := by omega
    have history : S2X.CheckpointVersionBinding (bytesOf e.saved.val) (bytesOf e.saved.deref.val) :=
      ⟨0,fun _=>bytesOf e.saved.val,[],rfl,rfl,by simp only [List.not_mem_nil,false_implies,implies_true]⟩
    have checkpointPair := F3S_CheckpointOnRun.log (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl) c.reserved
      e.run.p {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩} out output
      e.proof e.pub e.proof e.pub e.saved.deref e.saved p2 a2 after e.run.writer_call savedSize history rfl rfl effects
    have lowered := AuS1_Observe.lower (F3U_Oracle.hashv H)
      (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.proof () (Array.repeat 29#usize e.run.zero))
      (AuS1_Prepare.uniform _ _ _ _ (F3U_Oracle.hashv H) (fun _ _=>rfl) _ _ _ _) []
    simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at lowered
    have whole := congrArg Prod.fst (F3W_SourceLog.evaluated c base.boundaries s H e hashv first)
    dsimp only at whole
    rw [F3W_FirstLog.log c base.boundaries s H e hashv first,secondLog] at whole
    rw [F3S_ModelLog.schedule decoder H i p q data v guard parser queries found opening firstBatch.2]
    rw [whole,lowered,preparationLog,firstBatch.1,secondBatch.1]
    have glued := checkpointPair.trans modelCheckpoint
    have physicalEq : i.physical=⟨bytesOf e.pub.val⟩ := congrArg F3_Model.PhysicalPublic.mk physical
    rw [←physicalEq,←stored] at glued
    simpa only [List.append_assoc] using congrArg (fun l=>
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ++
      ((eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
        (l ++ (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1))) glued

#print axioms joined
end AspisR1.F3W_LogJoin
end

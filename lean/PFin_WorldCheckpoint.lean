import PFin_WorldEffects
import F3V_WriterModel
import F3S_CheckpointSplice
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldCheckpoint
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisR1CurrentCaller.InstalledPreparation
open MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem log {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (out : AspisR1PublicPreparation.verifier.Prepared) (same : currentPrepared out=e.run.p)
    (p2 : AspisR1Stage2.verifier.Prepared) (a2 : AspisR1Stage2.verifier.Accumulator)
    (reader : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops c.reserved)
      (VTop_Checkpoint.digest (D2 c H)) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,a2)))
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (preparedEq : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)
    (ten : CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
      {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩})=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) :
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (GExp_FirstCode.writerCode e.run.p {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩} e.proof e.pub) []).2 ++
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (GExq_RetainedReader.code c.reserved e.saved.deref e.proof e.pub .S2) []).2=
      (eval H (F3_Model.checkpoint ⟨bytesOf e.pub.val⟩ (bytesOf e.proof.val) p q tr i v)).1 := by
  have oracle := F3V_CheckpointOracle.oracle c H
  rw [←F3V_DigestCompatibility.same c H] at reader oracle
  obtain ⟨after,effects,modelCk⟩ := PFin_WorldEffects.stage _ c.reserved c.query c.geometry (D1 c H) ()
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run owner ports out same
    p2 a2 reader H oracle p i v q tr preparedEq ten
  have encoded := F3V_WriterModel.saved c B s H e owner ports out same
  have size : 32≤e.saved.val.length := by
    rw [encoded]
    simp only [Tx2N_Reader.writer,List.length_map,OraclePortCheckpointAbiC5.encode_length]
    decide
  have wrote := F3N_WriterReturned.erased (Tx1Q_Install.digest (D1 c H)) () _ _ e.proof e.pub e.saved e.run.writer_call
  have wp : CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared e.run.p)=F3K_CheckpointPreparedFields.writerPrepared out := by
    rw [←same]
    rfl
  rw [wp] at wrote
  have rawWriter : erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
      (CheckpointBytes5Writer.writer (F3K_CheckpointPreparedFields.writerPrepared out)
        (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator
          {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩})) e.proof e.pub)=ok e.saved.deref := by
    rw [←SdkC_Source.erasure (F3U_Oracle.hashv H) _ []]
    rw [SdkC_Source.erasure_to (VTop_Checkpoint.digest (Tx1Q_Install.digest (D1 c H))) ()
      (F3U_Oracle.hashv H) (fun _=>rfl)]
    exact wrote
  rw [F3S_CheckpointSplice.writer]
  have actual := F3S_CheckpointSplice.raw (F3U_Oracle.hashv H)
    (VTop_Checkpoint.digest (Tx1Q_Install.digest (D1 c H))) () (fun _=>rfl) c.reserved _ _
    e.proof e.pub e.saved p2 a2 after rawWriter size effects
  rw [←wp] at actual
  exact actual.trans modelCk

#print axioms log
end AspisR1.PFin_WorldCheckpoint
end

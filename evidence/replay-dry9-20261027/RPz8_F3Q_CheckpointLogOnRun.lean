import RPz8_F3Q_CheckpointStage
import RPz8_F3Q_Variant
import RPz8_F3N_CheckpointLog
import RPz7_WAdm_Inventory
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_CheckpointLogOnRun
open Aeneas Aeneas.Std Result AspisR1CurrentCaller.InstalledPreparation
open F3K_CheckpointPreparedFields Tx1Q_Carriers

theorem stage {C Hash : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed) (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (out : AspisR1PublicPreparation.verifier.Prepared) (same : currentPrepared out=run.p)
    (base : VTop_Stages.Ops) (proof2 pub2 checkpoint : Slice U8)
    (p2 : AspisR1Stage2.verifier.Prepared) (a2 : AspisR1Stage2.verifier.Accumulator)
    (reader : (Tx2N_Install.inner base reserved query).op18 (Tx1Q_Install.digest D) checkpoint proof2 pub2 .S2 hash=ok (.Ok (p2,a2)))
    (history : S2X.CheckpointVersionBinding (MultiproofConeCanonical.bytesOf saved.val) (MultiproofConeCanonical.bytesOf checkpoint.val))
    (proofSame : MultiproofConeCanonical.bytesOf proof2.val=MultiproofConeCanonical.bytesOf proof.val)
    (pubSame : MultiproofConeCanonical.bytesOf pub2.val=MultiproofConeCanonical.bytesOf pub.val)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash H)
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (preparedEq : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)
    (ten : CheckpointBytes5Output.accumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) :
    ∃ after,CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash
      (CheckpointBytes5Join.stage reserved (writerPrepared out)
        (CheckpointBytes3Namespaces.toAccumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) proof pub)
      []=ok (.Ok (p2,a2),after) ∧
      CheckpointBytes5Inputs.observe after=(AspisV8R19.MemoizedProgramLaw.eval H
        (F3_Model.checkpoint ⟨MultiproofConeCanonical.bytesOf pub.val⟩ (MultiproofConeCanonical.bytesOf proof.val) p q tr i v)).1 := by
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run installed reserved query geo D hash
    semantic pub proof split saved run owner ports
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  have success := F3Q_CheckpointStage.erased (Tx1Q_Install.digest D) hash base reserved query _ _ proof pub proof2 pub2
    checkpoint saved p2 a2 run.writer_call reader history proofSame pubSame
  obtain ⟨after,effects⟩ := F3Q_CheckpointStage.effects (Tx1Q_Install.digest D) hash _ _ proof pub reserved p2 a2 success
  have sameWriter : CheckpointBytes3Namespaces.toPrepared (prepared run.p)=writerPrepared out := by
    rw [←same]
    rfl
  rw [sameWriter] at effects
  have variant := F3Q_Variant.source out (by rw [same];exact fields.variant)
  have result := F3N_CheckpointLog.stage (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash H reserved out _ proof pub
    (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf pub.val) ⟨rfl,rfl,oracle⟩ variant size
    (by simpa only [writerPrepared,same,CheckpointBytes3Namespaces.toPrepared] using fields.queries)
    (by simpa only [writerPrepared,same,Port3_DecodeCoherence.inventory] using canonical)
    control.2.2.1 p2 a2 after effects p i v q tr preparedEq ten
  exact ⟨after,effects,result.2⟩

#print axioms stage
end AspisR1.F3Q_CheckpointLogOnRun
end

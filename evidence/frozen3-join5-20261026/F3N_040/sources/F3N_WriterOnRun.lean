import F3N_WriterNumeric
import WAdm_NativeInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_WriterOnRun
open Aeneas Aeneas.Std Result AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open F3K_CheckpointPreparedFields Tx1Q_Carriers

theorem saved {C Hash : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed) (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (same : currentPrepared out=run.p) :
    (WAdm_NativeInstall.install installed).op16 D run.p
      {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} proof pub hash=ok saved ∧
    saved=Tx2N_Reader.writer H (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf pub.val)
      (F3L_SourcePrepared.numeric out)
      (CheckpointBytes5Output.accumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) := by
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run installed reserved query geo D hash
    semantic pub proof split saved run owner ports
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  constructor
  · exact WAdm_NativeInstall.on_run installed reserved query geo D hash semantic pub proof split saved run owner ports
  · apply F3N_WriterNumeric.saved (Tx1Q_Install.digest D) hash H oracle out _ proof pub saved size
      (by simpa only [writerPrepared,same] using fields.queries)
      (by simpa only [writerPrepared,same,Port3_DecodeCoherence.inventory] using canonical)
      (by exact control.2.2.1)
    rw [same]
    exact run.writer_call

#print axioms saved
end AspisR1.F3N_WriterOnRun
end

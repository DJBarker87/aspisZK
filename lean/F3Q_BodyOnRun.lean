import F3N_ModelBody
import WAdm_Inventory
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_BodyOnRun
open Aeneas Aeneas.Std Result AspisR1CurrentCaller.InstalledPreparation
open F3K_CheckpointPreparedFields Tx1Q_Carriers

theorem body {C Hash : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed) (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (out : AspisR1PublicPreparation.verifier.Prepared) (same : currentPrepared out=run.p)
    (hp hu : Array U8 32#usize) :
    CheckpointBytesDecodeC5.sourceBody (writerPrepared out)
      (CheckpointBytes3Namespaces.toAccumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) hp hu=
      OraclePortCheckpointAbiC5.body (F3L_SourcePrepared.numeric out)
        (CheckpointBytes5Output.accumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}))
        (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu) := by
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run installed reserved query geo D hash
    semantic pub proof split saved run owner ports
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  exact F3L_WriterBody.body out _ hp hu size
    (by simpa only [writerPrepared,same,CheckpointBytes3Namespaces.toPrepared] using fields.queries)
    (by simpa only [writerPrepared,same,Port3_DecodeCoherence.inventory] using canonical) control.2.2.1

#print axioms body
end AspisR1.F3Q_BodyOnRun
end

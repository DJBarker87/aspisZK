import WAdm_OriginalEndpoint
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Effects
open Tx1Q_Carriers CheckpointBytes3Namespaces CheckpointBytes5Effect

/-- Ordered proof/public/checksum execution is constructed from this SAME
successful writer and state. This adds no independently successful Code run. -/
theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run1 : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) (before : Log) :
    ∃ after, run (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash
      (WAdm_SourceWriter.code (toPrepared (prepared run1.p))
        (toAccumulator (accumulator {run1.out with weights := ⟨run1.flushed.val,run1.flushed.property⟩})) proof pub)
      before = ok (saved.deref,after) := by
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run installed reserved query geo D hash
    semantic pub proof split saved run1 owner ports
  have control := Tx1Q_Control.fields installed reserved query geo D hash
    semantic pub proof split saved run1
  obtain ⟨after,actual⟩ := Port3_CheckpointInstall.writer_run (Tx1Q_Install.digest D)
    (prepared run1.p) (accumulator {run1.out with weights := ⟨run1.flushed.val,run1.flushed.property⟩})
    proof pub hash saved run1.writer_call before
  refine ⟨after,?_⟩
  rw [WAdm_SourceWriter.run_eq _ _ _ _ _ _
    (by simpa only [toAccumulator,mapVec,List.length_map] using size) fields.queries canonical]
  · exact actual
  · change toVariant (prepared run1.p).variant = _
    rw [fields.variant]
    rfl
  · exact control.2.2.1

#print axioms on_run
end AspisR1.WAdm_Effects
end

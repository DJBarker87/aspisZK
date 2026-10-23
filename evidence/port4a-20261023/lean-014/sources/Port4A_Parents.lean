import Port4A_CheckpointRows
import Port4A_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_Parents
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}

/-- Same inherited parent dictionary, with CURRENT reader control and explicit
retained helper interpretations. Writer remains reference. -/
def installed (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : Ops :=
  Port4A_ReaderInstall.install
    (Port3_NativeWriterShape.installed base reserved batch geometry query finish) reserved

theorem prefix_iff (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator) :
    VTop_Provenance.WriterPrefix (installed base reserved batch geometry query finish)
      D hash semantic proof split none p a ↔
    VTop_Provenance.WriterPrefix (Port3_NativeWriterShape.installed base reserved batch geometry query finish)
      D hash semantic proof split none p a := by rfl

theorem checkpoint_source (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) :
    VTop_Checkpoint.CheckpointSourceJoin (installed base reserved batch geometry query finish)
      D hash reserved := by
  constructor
  · intro semantic proof pub split p a saved reached wrote
    obtain ⟨after,run⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash saved wrote []
    exact ⟨[],after,run⟩
  · intro ck proof pub p a accepted
    exact Port4A_ReaderInstall.accepted_source _ reserved D hash ck proof pub .S2 p a accepted

#print axioms prefix_iff
#print axioms checkpoint_source
end AspisR1.Port4A_Parents
end

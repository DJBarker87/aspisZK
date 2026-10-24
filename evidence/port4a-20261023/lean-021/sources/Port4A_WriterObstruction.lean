import Port4A_Variant
import Port3_WriterBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_WriterObstruction
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}

/-- A constructive reached-input header disagreement for the unconstrained
preparation dictionary. The native Rust tag is selected by Prepared.variant;
the fixed S2 reference emits2. This is not a shipped preparation forgery. -/
theorem reached_tag_mismatch (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) (hp hu : Array U8 32#usize) :
    ∃ base', VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base' reserved batch geometryOps queryOps finish)
      D hash semantic proof split none (Port4A_Variant.relabel p) a ∧
      OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier.body_byte
        (CheckpointBytes3Namespaces.toPrepared (Port4A_Variant.relabel p))
        (CheckpointBytes3Namespaces.toAccumulator a) hp hu 8#usize ≠
        ok (Port3_WriterBoundary.shippedTag
          (CheckpointBytes3Namespaces.toPrepared (Port4A_Variant.relabel p)).variant) := by
  obtain ⟨base',prefix⟩ := Port4A_Variant.relabel_prefix base reserved batch geometryOps queryOps finish
    D hash semantic proof split p a reached
  exact ⟨base',prefix,Port3_WriterBoundary.not_shipped_tag _ _ hp hu rfl⟩

#print axioms reached_tag_mismatch
end AspisR1.Port4A_WriterObstruction
end

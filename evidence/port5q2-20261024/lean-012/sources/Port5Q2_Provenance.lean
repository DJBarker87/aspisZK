import Port5Q2_Ten

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_Provenance
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces
open Port4C_QueryState (FK FE)
variable {CoreError W : Type}

/-- Reached checkpoint provenance is CONSTRUCTED, not a premise. Immutable
Prepared is the same raw inventory; binding it to a frozen2 context is the
preparation owner's remaining semantic port. The accumulator is derived from
the actual ten calls and flush under the explicit local observation binding. -/
theorem reached (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (prepare : Port5Q2_Prepared.SessionAPrepare base)
    (basis : Port4C_BasisOuter.SessionABasis queryOps)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends queryOps)
    (lineCanonical : ∀ alpha values inverses value,
      queryOps.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached1 : VTop_Provenance.WriterPrefix
      (Port4C_Installed.installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    ∃ fields : Port5Q2_Prepared.PreparedFields p,
    ∃ size : a.weights.val.length=64,
    ∃ canonical : CheckpointBytesBlocks.CanonicalFields
      (Port3_DecodeCoherence.inventory p a size fields.queries),
    ∃ (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry),
    ∀ m : OraclePortCheckpointStateC3.Prepared FK FE,
      Port5Q2_Advance.ObservationBinding (Port3_QueryStage.release queryOps)
        proof p g (Port3_QueryInstall.observer none) geometry m →
      CheckpointBytes5Join.S1S7S8StateProvenance (toPrepared p) (toAccumulator a)
        (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical)
        (OraclePortCheckpointStateC3.write m).accumulator := by
  obtain ⟨fields,_,_,next,size,canonical⟩ := Port5Q2_Prepared.reached base reserved batch
    geometryOps queryOps finish prepare basis arithmetic lineCanonical D hash semantic proof split p a reached1
  obtain ⟨g,geometry,ten⟩ := Port5Q2_Ten.reached base reserved batch geometryOps queryOps finish
    prepare basis arithmetic lineCanonical D hash semantic proof split p a reached1
  refine ⟨fields,size,canonical,g,geometry,?_⟩
  intro m binding
  refine ⟨?_,?_,fields.queries,canonical,next,rfl,?_⟩
  · change toVariant p.variant=_
    rw [fields.variant]; rfl
  · simpa only [toAccumulator,mapVec,List.length_map] using size
  · exact (Port3_DecodeCoherence.accumulator_coherent p a size fields.queries canonical next).trans
      (ten m binding)

#print axioms reached
end AspisR1.Port5Q2_Provenance
end

import Port6CK_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_SourceJoin
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces
variable {CoreError W : Type}

/-- Actual current-helper18 plus the unchanged admitted reference8 selector,
instantiating the existing verifier-top source interface. No whole-op law is
an argument. Native ABI/ELF adoption has the same scope as Checkpoint.accepted. -/
theorem source (base : Ops) (reserved : Bool) (panic : Port6CK_Checkpoint.Panic)
    (batch : Port3_NativeBatchBody.Ops) (geometry : Port3_NativeGeometryBody.Ops CoreError)
    (query : Port3_NativeQueryBody.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) :
    VTop_Checkpoint.CheckpointSourceJoin
      (Port6CK_Checkpoint.installed base reserved panic batch geometry query finish) D hash reserved := by
  constructor
  · intro semantic proof pub split p a saved reached wrote
    obtain ⟨after,called⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash saved wrote []
    exact ⟨[],after,called⟩
  · intro ck proof pub p a resumed
    have retained := Port6CK_Reader.accepted reserved (Port6CK_Checkpoint.unwrap panic)
      (fun _ _ => rfl) D hash ck proof pub p a resumed
    exact Port4A_ReaderInstall.accepted_source base reserved D hash ck proof pub .S2 p a retained

/-- Existing verifier-top writer provenance is constructed only at the SAME
reached prefix; no arbitrary-state writer statement is asserted. -/
theorem provenance (base : Ops) (reserved : Bool) (panic : Port6CK_Checkpoint.Panic)
    (batch : Port3_NativeBatchBody.Ops) (geometry : Port3_NativeGeometryBody.Ops CoreError)
    (query : Port3_NativeQueryBody.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (prepare : Port5Q2_Prepared.SessionAPrepare base)
    (basis : Port4C_BasisOuter.SessionABasis query)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends query)
    (lineCanonical : ∀ alpha values inverses value,
      query.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) :
    VTop_Checkpoint.WriterProvenance
      (Port6CK_Checkpoint.installed base reserved panic batch geometry query finish)
      D hash semantic proof split := by
  intro p a reached1
  have reached := (Port6CK_Prefix.same
    (Port4C_Installed.installed base reserved batch geometry query finish)
    reserved (Port6CK_Checkpoint.unwrap panic) D hash semantic proof split p a).mp reached1
  obtain ⟨fields,_,_,next,size,canonical⟩ := Port5Q2_Prepared.reached base reserved batch geometry query finish
    prepare basis arithmetic lineCanonical D hash semantic proof split p a reached
  refine ⟨CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size fields.queries) canonical,
    CheckpointBytesBlocks.accumulator (Port3_DecodeCoherence.inventory p a size fields.queries) canonical,
    ?_,?_,fields.queries,canonical,next,rfl,rfl⟩
  · change toVariant p.variant=_
    rw [fields.variant]
    rfl
  · simpa only [toAccumulator,mapVec,List.length_map] using size

#print axioms source
#print axioms provenance
end AspisR1.Port6CK_SourceJoin
end

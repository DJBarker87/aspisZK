import Port4A_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_Variant
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}

def relabel (p : verifier.Prepared) : verifier.Prepared := {p with variant := .S1}

theorem query_invariant (ops : Port3_NativeQueryBody.Ops) (p : verifier.Prepared)
    (proof : Slice U8) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry : verifier.QueryGeometry) (b : verifier.BatchedWeights) (end1 : Usize) :
    Port3_QueryStage.query ops proof (relabel p) a g none geometry b end1 =
      Port3_QueryStage.query ops proof p a g none geometry b end1 := by rfl

theorem batch_invariant (ops : Port3_NativeBatchBody.Ops) (p : verifier.Prepared)
    {H : Type} (D : aspis_core.digest.Digest32 H) (proof : Slice U8)
    (root : Array U8 32#usize) (n : Usize) (hash : H) :
    Port3_BatchStage.batch ops D proof (relabel p) root n hash =
      Port3_BatchStage.batch ops D proof p root n hash := by rfl

/-- A reached prefix can be relabelled S1 by changing ONLY the uninstalled
preparation child. This exposes the variant gate missing from the parameterized
parent dictionary, and is not a claim about the actual concrete preparation. -/
theorem relabel_prefix (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    ∃ base', VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base' reserved batch geometryOps queryOps finish)
      D hash semantic proof split none (relabel p) a := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached
  let base' : Ops := {base with op7 := fun {_} _ _ _ _ _ _ => ok (.Ok (relabel p),g)}
  refine ⟨base',zero,g,.Ok (relabel p),initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,rfl,rfl,hinit,?_,hgeom,hpending,?_,hflush,hw,hr,hp,hn⟩
  · change Port3_BatchStage.batch batch D proof (relabel p) root 0#usize hash = _
    rw [batch_invariant]; exact hbatch
  · change Port3_QueryStage.query (Port3_NativeRowFrame.install queryOps)
      proof (relabel p) initial g none geometry pending split = _
    rw [query_invariant]; exact hquery

/-- The unqualified all-base provenance claim is false whenever its intended
reached class is inhabited. A concrete preparation binding is necessary. -/
theorem not_uniform_provenance (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    ¬ (∀ base', VTop_Checkpoint.WriterProvenance
      (Port3_NativeWriterShape.installed base' reserved batch geometryOps queryOps finish)
      D hash semantic proof split) := by
  obtain ⟨base',reached'⟩ := relabel_prefix base reserved batch geometryOps queryOps finish
    D hash semantic proof split p a reached
  intro all
  obtain ⟨pm,am,prov⟩ := all base' (relabel p) a reached'
  have bad := prov.variant
  cases bad

#print axioms not_uniform_provenance

#print axioms query_invariant
#print axioms batch_invariant
#print axioms relabel_prefix
end AspisR1.Port4A_Variant
end

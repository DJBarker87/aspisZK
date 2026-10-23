import Port4A_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_PrepareCut
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}

/-- The exact preparation return from the SAME prefix; it is never replaced
by an independently successful preparation or a separately chosen Prepared. -/
theorem returned (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base reserved batch geometry query finish)
      D hash semantic proof split none p a) :
    ∃ zero g, base.op1=ok zero ∧
      base.op7 D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) := by
  obtain ⟨zero,g,prep,initial,root,geom,pending,out,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,rest⟩ := reached
  cases prep with
  | Err e => cases hbranch
  | Ok value =>
    have same : value=p := by cases Result.ok.inj hbranch; rfl
    subst value
    exact ⟨zero,g,hzero,hprep⟩

/-- Correct local variant statement: a concrete preparation leaf must supply
its variant law. This law is EXPLICITLY retained, not discharged here. -/
theorem variant_of_prepare (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (prepareVariant : ∀ zero g p, base.op7 D semantic proof hash none
      (Array.repeat 29#usize zero)=ok (.Ok p,g) → p.variant=.S2)
    (reached : VTop_Provenance.WriterPrefix
      (Port3_NativeWriterShape.installed base reserved batch geometry query finish)
      D hash semantic proof split none p a) : p.variant=.S2 := by
  obtain ⟨zero,g,_,prepared⟩ := returned base reserved batch geometry query finish
    D hash semantic proof split p a reached
  exact prepareVariant zero g p prepared

#print axioms returned
#print axioms variant_of_prepare
end AspisR1.Port4A_PrepareCut
end

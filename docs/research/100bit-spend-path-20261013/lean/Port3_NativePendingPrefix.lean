import Port3_NativePendingInstall

/-! The source/reference constructor equality is used only on the input
reached by the same installed TX1 prefix. No global op10 equality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativePendingPrefix
open Aeneas Aeneas.Std Result VTop_Stages

theorem prefix_to_reference (base : Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix (Port3_NativePendingInstall.installed base reserved aops qops)
      D hash semantic proof split obs p a) :
    VTop_Provenance.WriterPrefix (Port3_WriterShape.installed base reserved aops qops)
      D hash semantic proof split obs p a := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached
  have hi : Port3_Initial.constructor reserved .S2=ok (.Ok initial) := by
    change Port3_Constructor.extracted (Port3_Constructor.leaves reserved) .S2 = _ at hinit
    rw [Port3_Constructor.normalization] at hinit
    exact hinit
  have fields := Port3_Initial.accepted_fields base reserved initial hi
  have size : initial.weights.deref.val.length=64 := by
    change initial.weights.val.length=64
    rw [fields.2.1,List.length_replicate]
  have native := Port3_NativePendingInstall.reference_eq reserved initial.weights.deref size
  change Port3_NativePendingInstall.source reserved initial.weights.deref=ok (.Ok pending) at hpending
  rw [native] at hpending
  exact ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩

theorem reached_shape (base : Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix (Port3_NativePendingInstall.installed base reserved aops qops)
      D hash semantic proof split none p a) :
    reserved=true ∧ split.val=10 ∧ a.next.val=10 ∧ a.weights.val.length=64 ∧
      ∀ q ∈ a.weights.val, Port3_FlushInstall.Canonical q :=
  Port3_WriterShape.reached_shape base reserved aops qops D hash semantic proof split p a
    (prefix_to_reference base reserved aops qops D hash semantic proof split none p a reached)

#print axioms prefix_to_reference
#print axioms reached_shape
end AspisR1.Port3_NativePendingPrefix
end

import Port4D_FinishInstall
import Port3_NativeQueryRaw

/-! The current native flush parent is installed at the SAME writer prefix.
Its length requirement follows from the native query/pending frames. The
value reducer and S7 push remain explicit local interpretations; checkpoint
8/18 remain reference. No independent flush or query run is chosen. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FlushPrefix
open Aeneas Aeneas.Std Result VTop_Stages

variable {CoreError W : Type}

def installed (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : Ops :=
  Port4D_FinishInstall.installed base reserved batch geometry (Port3_NativeRowFrame.install query) finish

theorem reached_shape (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix (installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    reserved=true ∧ split.val=10 ∧ a.next.val=10 ∧ a.weights.val.length=64 ∧
      ∀ q ∈ a.weights.val, Port3_FlushInstall.Canonical q := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached
  have hsplit : split.val = 10 := by
    have e : (10#usize : Usize) = sv := Result.ok.inj hs
    subst sv
    exact hsv
  have hi : Port3_Initial.constructor reserved .S2 = ok (.Ok initial) := by
    change Port3_Constructor.extracted (Port3_Constructor.leaves reserved) .S2 = _ at hinit
    rw [Port3_Constructor.normalization] at hinit
    exact hinit
  have initialFields := Port3_Initial.accepted_fields base reserved initial hi
  have initialSize : initial.weights.val.length=64 := by rw [initialFields.2.1,List.length_replicate]
  have pendingFields := Port3_NativePendingInstall.accepted_fields reserved initial.weights.deref pending
    initialSize hpending
  have pendingSize : pending.raw.val.length=64 := pendingFields.2.2.2
  have native := (Port3_QueryInstall.success_iff _ _).mp hquery
  have query := Port3_NativeQueryRaw.loop_raw (Port3_QueryStage.release queryOps)
    proof p initial returned.1 g none geometry pending returned.2 split initialSize pendingSize
    (by rw [initialFields.2.2.2.2]; simp) native
  have returnedSize : returned.1.weights.val.length=64 := by rw [query.1]; exact initialSize
  have lengths : returned.1.weights.deref.val.length ≤ returned.2.raw.val.length := by
    change returned.1.weights.val.length ≤ returned.2.raw.val.length
    rw [returnedSize,query.2.1]
  have hflush : Port3_FlushInstall.flush returned.2 returned.1.weights.deref = ok flushed :=
    (Port4D_FlushABI.reference_eq returned.2 returned.1.weights.deref lengths).symm.trans hflush
  have flushedFields := Port3_FlushInstall.accepted_contents returned.2 returned.1.weights.deref flushed lengths hflush
  have canonical := Port3_FlushInstall.accepted_canonical returned.2 returned.1.weights.deref flushed lengths hflush
  refine ⟨initialFields.1,hsplit,?_,?_,?_⟩
  · rw [hn,query.2.2,hsplit]
  · rw [hw,flushedFields.2]; exact returnedSize
  · rw [hw]; exact canonical

/-- The returned writer input comes from the same accepted TX1 execution. -/
theorem accepted_shape (base : Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 (installed base reserved batch geometryOps queryOps finish)
      D semantic pub proof split hash none = ok (.Ok saved)) :
    ∃ p a, VTop_Provenance.WriterPrefix (installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a ∧
      (installed base reserved batch geometryOps queryOps finish).op8 D p a proof pub hash = ok saved ∧
      reserved=true ∧ split.val=10 ∧ a.next.val=10 ∧ a.weights.val.length=64 ∧
      ∀ q ∈ a.weights.val, Port3_FlushInstall.Canonical q := by
  obtain ⟨p,a,reached,wrote⟩ := VTop_Provenance.writer_prefix _ D hash semantic pub proof split none saved accepted
  exact ⟨p,a,reached,wrote,reached_shape base reserved batch geometryOps queryOps finish D hash semantic proof split p a reached⟩

#print axioms reached_shape
#print axioms accepted_shape
end AspisR1.Port4D_FlushPrefix
end

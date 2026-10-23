import Port3_BatchStage
import Port3_GeometryStage
import Port3_QueryStage
import Port3_FinishStage

/-! One parent dictionary. Checkpoint ops8/18 remain explicitly REFERENCE;
flush uses retained mutable S8 with its named lowering gate. Local native
leaves and owner preparation are visible parameters, not correctness axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_Parents
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}

def installed (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : Ops :=
  {base with
    op5 := Port3_BatchStage.batch batch
    op6 := Port3_QueryStage.query query
    op8 := Port3_CheckpointInstall.writer
    op9 := Port3_FlushInstall.flush
    op10 := Port3_NativePendingInstall.source reserved
    op11 := Port3_GeometryStage.geometry geometry
    op12 := fun v => Port3_Constructor.extracted (Port3_Constructor.leaves reserved) v
    op16 := ok 10#usize
    op18 := Port3_CheckpointInstall.reader reserved
    op19 := Port3_FinishStage.finish finish}

/-- No agreement predicate or whole-operation equality hypothesis is needed
for these parent choices. This theorem intentionally says reference at8/18. -/
theorem installation (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) :
    let ops := installed base reserved batch geometry query finish
    ops.op5=Port3_BatchStage.batch batch ∧ ops.op6=Port3_QueryStage.query query ∧
    ops.op8=Port3_CheckpointInstall.writer ∧ ops.op9=Port3_FlushInstall.flush ∧
    ops.op10=Port3_NativePendingInstall.source reserved ∧
    ops.op11=Port3_GeometryStage.geometry geometry ∧
    ops.op12=(fun v => Port3_Constructor.extracted (Port3_Constructor.leaves reserved) v) ∧
    ops.op18=Port3_CheckpointInstall.reader reserved ∧
    ops.op19=Port3_FinishStage.finish finish := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The physical writer input's counter and actual preflush size come from
ONE installed prefix. No arithmetic/canonical/provenance witness is assumed. -/
theorem reached_control (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : VTop_Provenance.WriterPrefix (installed base reserved batch geometry query finish)
      D hash semantic proof split none p a) :
    reserved=true ∧ split.val=10 ∧ a.next.val=10 := by
  obtain ⟨zero,g,prep,initial,root,geom,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached
  have hsplit : split.val=10 := by
    have e : (10#usize : Usize)=sv := Result.ok.inj hs
    subst sv
    exact hsv
  have hi : Port3_Initial.constructor reserved .S2=ok (.Ok initial) := by
    change Port3_Constructor.extracted (Port3_Constructor.leaves reserved) .S2=_ at hinit
    rw [Port3_Constructor.normalization] at hinit
    exact hinit
  have fields := Port3_Initial.accepted_fields base reserved initial hi
  have control := Port3_QueryStage.loop_fields query proof p initial returned.1 g none geom
    pending returned.2 split (by rw [fields.2.2.2.2]; simp) hquery
  refine ⟨fields.1,hsplit,?_⟩
  rw [hn,control.2,hsplit]

#print axioms installation
#print axioms reached_control
end AspisR1.Port3_Parents
end

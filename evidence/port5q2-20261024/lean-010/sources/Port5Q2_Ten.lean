import Port5Q2_Prepared
import Port5Q2_Advance

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_Ten
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Output (ofK ofE)
open Port4C_QueryState (state FK FE)

/-- The virtual source sum starts at the SAME physical weights, with the
checkpoint decoder's default and modulo behavior retained. -/
theorem initial_state (a : verifier.Accumulator) :
    state a (S7Kani3CallerTrace.initialSum (Port3_PendingInstall.owned a.weights.deref))=
      CheckpointBytes5Output.accumulator a := by
  unfold state CheckpointBytes5Output.accumulator
  congr 1
  funext i
  unfold Port4C_SumField.weight
  simp only [S7Kani3CallerTrace.initialSum,Port3_PendingInstall.owned,
    Port3_FlushInstall.toWeights,List.getElem?_map]
  change (⟨⟨_,_⟩,⟨_,_⟩⟩ : FK) = ofK ((a.weights.val[i.val]?).getD (CheckpointBytes4ReaderFields.sourceK 0))
  change _ = _
  have deref : a.weights.deref.val=a.weights.val := rfl
  rw [deref]
  cases h : a.weights.val[i.val]? with
  | none => simp only [h,Option.map_none,Option.getD_none]; rfl
  | some q => simp only [h,Option.map_some,Option.getD_some]; rfl

variable {CoreError W : Type}
/-- The SAME prefix selects its actual g/geometry. Once their LOCAL observed
values/basis are bound, its physical writer accumulator is exactly ten steps.
No whole-query or ten-step equality is assumed. -/
theorem reached (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (prepare : Port5Q2_Prepared.SessionAPrepare base)
    (basisBackend : Port4C_BasisOuter.SessionABasis queryOps)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends queryOps)
    (lineCanonical : ∀ alpha values inverses value,
      queryOps.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached1 : VTop_Provenance.WriterPrefix
      (Port4C_Installed.installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    ∃ (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry),
      ∀ m : OraclePortCheckpointStateC3.Prepared FK FE,
      Port5Q2_Advance.ObservationBinding (Port3_QueryStage.release queryOps)
        proof p g (Port3_QueryInstall.observer none) geometry m →
      CheckpointBytes5Output.accumulator a=(OraclePortCheckpointStateC3.write m).accumulator := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached1
  have prepared : base.op7 D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) := by
    cases prep with
    | Err e => cases hbranch
    | Ok value =>
      have same : value=p := by cases Result.ok.inj hbranch; rfl
      subst value
      exact hprep
  have pf := prepare.accepted D hash semantic proof zero g p hzero prepared
  have splitValue : split.val=10 := by
    have eq : (10#usize : Usize)=sv := Result.ok.inj hs
    subst sv
    exact hsv
  have init : Port3_Initial.constructor reserved .S2=ok (.Ok initial) := by
    change Port3_Constructor.extracted (Port3_Constructor.leaves reserved) .S2=_ at hinit
    rw [Port3_Constructor.normalization] at hinit
    exact hinit
  have initialFields := Port3_Initial.accepted_fields base reserved initial init
  have size : initial.weights.val.length=64 := by rw [initialFields.2.1,List.length_replicate]
  have powerCanonical : Port3_FlushInstall.Canonical initial.power := by
    rw [initialFields.2.2.2.1]
    change (1 : Nat)<2147483647 ∧ 0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647
    decide
  have rhsCanonical : Port4C_QueryArithmetic.CanonE initial.rhs := by
    rw [initialFields.2.2.1]
    change ((0 : Nat)<2147483647 ∧ 0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647) ∧
      ((0 : Nat)<2147483647 ∧ 0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647)
    decide
  have pendingFields := Port4C_Pending.accepted reserved initial.weights.deref pending size hpending
  have native := (Port3_QueryInstall.success_iff _ _).mp hquery
  have commute : Port3_QueryStage.release (Port4C_RowStd.install queryOps)=
      Port4C_RowStd.install (Port3_QueryStage.release queryOps) := rfl
  rw [commute,Port3_NativeQueryFrame.loop_eq] at native
  have actual := Port2_QueryLoop.source_calls
    (Port3_NativeQueryBody.verifier.candidate.query_values
      (Port4C_RowStd.install (Port3_QueryStage.release queryOps))) proof p g
    (Port3_QueryInstall.observer none) geometry split
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields _ proof p a a1 g
      (Port3_QueryInstall.observer none) geometry b b1 h).2.2)
    initial returned.1 pending returned.2
    (by rw [initialFields.2.2.2.2,splitValue]; decide) native
  have start : initial.next.val=0 := by rw [initialFields.2.2.2.2]; rfl
  rw [start,splitValue,Nat.sub_zero] at actual
  have basis : Port4C_BasisOuter.SessionABasis (Port3_QueryStage.release queryOps) :=
    ⟨basisBackend.s3_s4_mul,basisBackend.s3_s4_sub,basisBackend.s3_s4_double,basisBackend.zero,basisBackend.one⟩
  have arithmetic1 : Port4C_QueryArithmetic.SessionABackends (Port3_QueryStage.release queryOps) :=
    ⟨arithmetic.s3_s4_s5_mulE,arithmetic.s3_s4_s5_addE,arithmetic.s3_s4_s9_mulK⟩
  refine ⟨g,geometry,?_⟩
  intro m binding
  obtain ⟨sumOut,trace,progress,meaning⟩ := Port5Q2_Advance.calls
    (Port3_QueryStage.release queryOps) basis arithmetic1
    (Port3_PendingInstall.owned initial.weights.deref) proof p g
    (Port3_QueryInstall.observer none) geometry 10 m binding
    initial returned.1 pending returned.2 10 0
    (S7Kani3CallerTrace.initialSum (Port3_PendingInstall.owned initial.weights.deref))
    size (by decide) powerCanonical pf.rho rhsCanonical lineCanonical
    pendingFields.2.2.2.2.1 pendingFields.2.2.2.2.2 actual
  have weights := Port3_QueryFrame.calls_weights _ _ _ _ _ _ _
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields _ proof p a a1 g
      (Port3_QueryInstall.observer none) geometry b b1 h).2.1) actual
  have returnedSize : returned.1.weights.val.length=64 := by rw [weights]; exact size
  change Port3_FlushInstall.flush returned.2 initial.weights.deref=ok flushed at hflush
  have exactFlush := Port4C_FlushState.exact_state
    (Port3_PendingInstall.owned initial.weights.deref) returned.1 returned.2 sumOut flushed
    returnedSize progress.2.1 trace (by simpa only [weights] using hflush)
  have physical : a={returned.1 with weights:=⟨flushed.val,flushed.property⟩} := by
    cases a
    congr 1
    · exact Subtype.ext hw
  rw [physical,exactFlush,meaning,initial_state,Port3_Initial.accepted_initial base reserved initial init]
  exact OraclePortCheckpointStateC3.advance_run m 10 0

#print axioms initial_state
#print axioms reached
end AspisR1.Port5Q2_Ten
end

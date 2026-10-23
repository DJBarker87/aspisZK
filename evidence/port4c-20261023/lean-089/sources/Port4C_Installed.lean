import Port3_Parents
import Port4C_Pending
import Port4C_GeometryInverse
import Port4C_FlushField

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_Installed
open Aeneas Aeneas.Std Result VTop_Stages
variable {CoreError W : Type}

def installed (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : Ops :=
  Port3_Parents.installed base reserved batch
    (Port4C_GeometryInverse.install {geometry with op0 := OraclePortStdBuilder.fromFn})
    (Port4C_RowStd.install query) finish

/-- This SAME installed prefix derives writer rhs/power and all weight
canonicality from initial/pending/query/flush, retaining preparation rho and
primitive session A ports explicitly. No successful alternate query exists. -/
theorem writer_fields (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (basisBackend : Port4C_BasisOuter.SessionABasis queryOps)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends queryOps)
    (lineCanonical : ∀ alpha values inverses value,
      queryOps.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (rhoCanonical : Port3_FlushInstall.Canonical p.rho)
    (reached : VTop_Provenance.WriterPrefix
      (installed base reserved batch geometryOps queryOps finish)
      D hash semantic proof split none p a) :
    reserved=true ∧ split.val=10 ∧ a.next.val=10 ∧ a.weights.val.length=64 ∧
      Port4C_QueryArithmetic.CanonE a.rhs ∧ Port3_FlushInstall.Canonical a.power ∧
      (∀ q ∈ a.weights.val, Port3_FlushInstall.Canonical q) ∧
      ∃ sum : S7Kani3CallerTrace.Sum, ∀ i : Fin 64,
        (CheckpointBytes5Output.accumulator a).weights i=Port4C_SumField.weight sum i.val := by
  obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hw,hr,hp,hn⟩ := reached
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
    decide
  have rhsCanonical : Port4C_QueryArithmetic.CanonE initial.rhs := by
    rw [initialFields.2.2.1]
    decide
  have pendingFields := Port4C_Pending.accepted reserved initial.weights.deref pending size hpending
  have native := (Port3_QueryInstall.success_iff _ _).mp hquery
  have commute : Port3_QueryStage.release (Port4C_RowStd.install queryOps)=
      Port4C_RowStd.install (Port3_QueryStage.release queryOps) := rfl
  rw [commute] at native
  have basis : Port4C_BasisOuter.SessionABasis (Port3_QueryStage.release queryOps) :=
    ⟨basisBackend.s3_s4_mul,basisBackend.s3_s4_sub,basisBackend.s3_s4_double,basisBackend.zero,basisBackend.one⟩
  have arithmetic1 : Port4C_QueryArithmetic.SessionABackends (Port3_QueryStage.release queryOps) :=
    ⟨arithmetic.s3_s4_s5_mulE,arithmetic.s3_s4_s5_addE,arithmetic.s3_s4_s9_mulK⟩
  obtain ⟨sumOut,trace,progress,next,weights,rhs,power⟩ := Port4C_QueryLoop.loop
    (Port3_QueryStage.release queryOps) basis arithmetic1 (Port3_PendingInstall.owned initial.weights.deref)
    proof p initial returned.1 g (Port3_QueryInstall.observer none) geometry pending returned.2 split
    0 (S7Kani3CallerTrace.initialSum (Port3_PendingInstall.owned initial.weights.deref)) size
    (by rw [initialFields.2.2.2.2]; simp)
    (by rw [initialFields.2.2.2.2,splitValue]; decide)
    powerCanonical rhoCanonical rhsCanonical lineCanonical
    pendingFields.2.2.2.2.1 pendingFields.2.2.2.2.2 native
  have returnedSize : returned.1.weights.val.length=64 := by rw [weights]; exact size
  have rawSize : returned.2.raw.val.length=64 := progress.2.1
  have flushFields := Port4C_FlushField.accepted (Port3_PendingInstall.owned initial.weights.deref)
    returned.2 sumOut returned.1.weights.deref flushed returnedSize rawSize trace hflush
  have canonical := Port3_FlushInstall.accepted_canonical returned.2 returned.1.weights.deref
    flushed (by change returned.1.weights.val.length≤returned.2.raw.val.length; omega) hflush
  refine ⟨initialFields.1,splitValue,?_,?_,?_,?_,?_,sumOut,?_⟩
  · rw [hn,next,splitValue]
  · rw [hw]; exact flushFields.1
  · rw [hr]; exact rhs
  · rw [hp]; exact power
  · rw [hw]; exact canonical
  · intro i
    change CheckpointBytes5Output.ofK ((a.weights.val[i.val]?).getD
      (CheckpointBytes4ReaderFields.sourceK 0))=_
    rw [hw]
    exact flushFields.2 i

#print axioms writer_fields
end AspisR1.Port4C_Installed
end

import NBO_QueryRhs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_TopInstall
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Only the previously checked initialization/pending/query/flush/split
operations are installed; all preparation, authentication and geometry stay
on their original base dictionary. -/
def query (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
 (geometry : verifier.QueryGeometry) (b : verifier.BatchedWeights) (end1 : Usize) :=
 Port3_QueryInstall.result (verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g (Port3_QueryInstall.observer obs) geometry b end1)
def install (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops) : VTop_Stages.Ops :=
 {Port3_Initial.install base reserved with
   op6:=query ops
   op9:=Port3_FlushInstall.flush
   op10:=Port3_NativePendingInstall.source reserved
   op16:=ok 10#usize}
/-- Exact lower producer statements, on the SAME successful preparation and
geometry calls used by the actual top prefix. No final/query equality enters. -/
structure Producers (base : VTop_Stages.Ops) : Prop where
 prepared : ∀ {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) hash
   semantic proof initial preparation g p,
   base.op7 D semantic proof hash none initial=ok (preparation,g) →
   core.result.Result.Insts.CoreOpsTry.branch preparation=ok (.Continue p) →
   NBO_AcceptedTail.PreparedDomain p
 geometry : ∀ queries split geometry,
   split.val=10 → base.op11 queries 0#usize split=ok (.Ok geometry) →
   NBO_QueryDomains.GeometryDomain geometry
/-- SAME accepted writer prefix supplies constructors, query execution,
returned state and flush; the dependent rhs/phase/width properties are derived.
This is the installed model consumer, not a native whole-TX1 refinement. -/
theorem reached (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (producers : Producers base) (lower : NBO_QueryDomains.Lower ops)
 (fields : NBO_TailDomain.NBC_Fields ops)
 {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
 (prefixRun : VTop_Provenance.WriterPrefix (install base reserved ops)
   D hash semantic proof split none p a) :
 split.val=10 ∧ a.next.val=10 ∧ a.weights.val.length=64 ∧
 NBO_TailDomain.WideCanonical a.rhs ∧ NBF_PowerStep.Canonical a.power ∧
 (∀ q ∈ a.weights.val, Port3_FlushInstall.Canonical q) := by
 obtain ⟨zero,g,prep,initial,root,geometry,pending,returned,flushed,parsed,sv,
   hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
   hw,hr,hp,hn⟩ := prefixRun
 have split10 : split.val=10 := by
   have eq : (10#usize : Usize)=sv := Result.ok.inj hs
   subst sv;exact hsv
 have splitEq : split=10#usize := UScalar.eq_of_val_eq split10
 have prepared := producers.prepared D hash semantic proof (Array.repeat 29#usize zero)
   prep g p hprep hbranch
 have domain := producers.geometry p.queries split geometry split10 hgeom
 have initialRun : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok initial) := hinit
 have pendingRun : Port3_NativePendingInstall.source reserved initial.weights.deref=
   ok (.Ok pending) := hpending
 have queryRun : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p initial g none geometry pending 10#usize=ok (.Ok returned) := by
   change query ops proof p initial g none geometry pending split=_ at hquery
   unfold query at hquery
   have h := (Port3_QueryInstall.success_iff _ _).mp hquery
   simpa only [Port3_QueryInstall.observer,Option.map_none,splitEq] using h
 have good := NBO_QueryRhs.from_constructors base reserved ops lower fields proof p prepared
   g geometry domain initial returned.1 pending returned.2 initialRun pendingRun queryRun
 obtain ⟨next,terms,weights,raw,progress⟩ := NBF_QueryLoop.from_constructors base reserved ops
   fields.power proof p g geometry prepared.rho initial returned.1 pending returned.2
   initialRun pendingRun queryRun
 have length : flushed.val.length=64 :=
   (Port3_FlushInstall.accepted_contents returned.2 returned.1.weights.deref flushed
     (by change returned.1.weights.val.length≤returned.2.raw.val.length;omega) hflush).2.trans weights
 have canonical := Port3_FlushInstall.accepted_canonical returned.2 returned.1.weights.deref
   flushed (by change returned.1.weights.val.length≤returned.2.raw.val.length;omega) hflush
 exact ⟨split10,hn.trans (congrArg Usize.val rfl) |>.trans next,
   by rw [hw];exact length,by rw [hr];exact good.2,
   by rw [hp];exact good.1.power,by rw [hw];exact canonical⟩
#print axioms reached
end NBO_TopInstall
end

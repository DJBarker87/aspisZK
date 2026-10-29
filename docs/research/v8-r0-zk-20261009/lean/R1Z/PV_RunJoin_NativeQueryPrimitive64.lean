import R1Z.PV_RunJoin_QueryLoopTotal64
import R1Z.PV_RunJoin_NativeQueryExact63
/-! Source totality plus the actual query image, at primitive stored-state
bounds. Domain is still to be produced from context; it is not installed as a
new hypothesis of QueryAppend, Links, T, or the privacy endpoint. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeQueryPrimitive64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_PublishSkeleton54 (bytes)

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase.val) p)
    (domain : PV_RunJoin_QueryLoopTotal64.Domain cc1 cc2 (alloc.vec.Vec.deref p.folded_word) p.folded_salts)
    (out : alloc.vec.Vec U8) (offset : out.length=10055) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ next, prover.append_query_openings out cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word)
      p.folded_salts=ok next ∧
      bytes next.val=ProverCommitPublish43.queries (PV_RunJoin_ActualRun.plans phase.val).queries (bytes out.val) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have range : PV_RunJoin_PublishSkeleton57.QueryRange p.queries := by
    obtain ⟨prepared,salts,hp,hs,hf⟩ := context
    exact PV_RJQ_QueryRange.actual PV_RunJoin_ActualRun.runs phase.val prepared salts p hp hs hf
  obtain ⟨next,hn,hlen⟩ := PV_RunJoin_QueryLoopTotal64.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    cc1 cc2 p.queries range (alloc.vec.Vec.deref p.folded_word) p.folded_salts domain out
    (by rw [offset];scalar_tac)
  exact ⟨next,hn,PV_RunJoin_NativeQueryExact63.complete base heap box ops runtime world phase p
    cc1 cc2 hc1 hc2 context out next offset hn⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeQueryPrimitive64

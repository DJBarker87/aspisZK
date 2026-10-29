import R1Z.PV_RunJoin_QueryExact63
import R1Z.PV_RunJoin_NativeActual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeQueryExact63
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
    (out next : alloc.vec.Vec U8) (offset : out.length=10055)
    (success : @prover.append_query_openings (types base) (opsNative base heap box ops runtime world)
      out cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    bytes next.val=ProverCommitPublish43.queries
      (PV_RunJoin_ActualRun.plans phase.val).queries (bytes out.val) :=
  PV_RunJoin_QueryExact63.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) phase.val p cc1 cc2 hc1 hc2 context out next offset success

#print axioms complete
end R1Z.PV_RunJoin_NativeQueryExact63

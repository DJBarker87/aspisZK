import R1Z.PV_RunJoin_QuerySize63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryCellComplete63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

/-- Actual source success alone determines the exact 832-byte cell. No output
length or byte equality is a premise of this source-image theorem. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (phase : @PV_RunJoin_NativeControl55.Phase (types base))
    (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (selected base heap box ops)
      (@PV_RunJoin_ActualRun.runs (types base) (selected base heap box ops) phase) p)
    (range : PV_RunJoin_PublishSkeleton57.QueryRange p.queries)
    (i : Fin 22) (payload : alloc.vec.Vec U8)
    (success : @PV_RunJoin_ActualPlanSources59.queryBytes (types base)
      (selected base heap box ops) p (PV_RunJoin_QueryCell63.index i)=ok payload)
    (out : alloc.vec.Vec U8) (room : out.length+832≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ next, prover.append_query_openings_loop.body cc1 cc2 p.queries
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts out (PV_RunJoin_QueryCell63.index i)=
      ok (.cont (next,Usize.wrapping_add (PV_RunJoin_QueryCell63.index i) 1#usize)) ∧
      PV_RunJoin_PublishSkeleton54.bytes next.val=PV_RunJoin_PublishSkeleton54.bytes out.val ++
        ProverCommitPublish43.queryBytes (PV_RunJoin_ActualPlanSources59.queryPart phase i) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have script := PV_RunJoin_QueryCell63.source base heap box ops p cc1 cc2 hc1 hc2 i payload success
  have size := PV_RunJoin_QuerySize63.script base heap box ops cc1 cc2 p.queries range
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts i PV_RunJoin_ActualPlanSources59.empty
  rw [script] at size
  change payload.length=0+832 at size
  exact PV_RunJoin_QueryCell63.actual base heap box ops phase p cc1 cc2 hc1 hc2 context i payload success
    (by omega) out room

#print axioms complete
end R1Z.PV_RunJoin_QueryCellComplete63

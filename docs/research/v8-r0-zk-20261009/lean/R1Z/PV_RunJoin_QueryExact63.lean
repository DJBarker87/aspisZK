import R1Z.PV_RunJoin_QueryChainImage63
import R1Z.PV_RJQ_QueryRange
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryExact63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54 (bytes)

/-- Complete ordered query bytes of a successful native append. Context and
range come from this exact prepare/salt/finish sequence. Success totality is
not inferred from this theorem and remains part of the original QueryAppend. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (phase : @PV_RunJoin_NativeControl55.Phase (types base))
    (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (selected base heap box ops)
      (@PV_RunJoin_ActualRun.runs (types base) (selected base heap box ops) phase) p)
    (out next : alloc.vec.Vec U8) (offset : out.length=10055)
    (success : @prover.append_query_openings (types base) (selected base heap box ops)
      out cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    bytes next.val=ProverCommitPublish43.queries (PV_RunJoin_ActualRun.plans phase).queries (bytes out.val) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have range : PV_RunJoin_PublishSkeleton57.QueryRange p.queries := by
    obtain ⟨prepared,salts,hp,hs,hf⟩ := context
    exact PV_RJQ_QueryRange.actual PV_RunJoin_ActualRun.runs phase prepared salts p hp hs hf
  have room : out.length+832*22≤Usize.max := by
    rw [offset]
    scalar_tac
  change prover.append_query_openings_loop out cc1 cc2 p.queries
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts 0#usize=ok next at success
  rw [PV_RunJoin_QueryLoop63.loop base heap box ops cc1 cc2 p.queries range
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts 22 0#usize out rfl room] at success
  have image := PV_RunJoin_QueryChainImage63.complete base heap box ops phase p cc1 cc2 hc1 hc2 context range
    22 0#usize out next rfl room success
  rw [PV_RunJoin_QueryStream63.plan]
  exact image

#print axioms complete
end R1Z.PV_RunJoin_QueryExact63

import R1Z.PV_RunJoin_PublishContext57
/-! D494/(v) correction candidate for the unchanged NodeAppend quantifier.
The existing PV_RunJoin_ links remain read-only. QueryRange and QueryContext
are separate named links in the existing Context57 interface. This local
candidate does not assert a simultaneous-link witness or a decomposition. -/
set_option autoImplicit false
namespace R1Z.PV_RJN_NodeContext
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
open PV_RunJoin_PublishSkeleton57 (QueryRange)
open PV_RunJoin_PublishContext57 (QueryContext)
variable [ExternalTypes] [ExternalFuns]
/-- Original requirements, restricted to in-range publications returned by
this run's prepare/private-salts/finish sequence. No requirement is dropped. -/
def PV_RJN_Link_NodeAppend {I : Type} (runs : I → Run) : Prop :=
  ∀ i (p : prover.Publication), Fields (runs i) p → QueryRange p.queries → QueryContext (runs i) p →
  (runs i).plan.slots.length=6 ∧
  (∀ begin1 end1 folded, begin1.val≤end1.val → end1.val≤22 →
    ∃ idx, prover.publication_indices p.queries begin1 end1 folded=ok idx ∧
      idx.val.map UScalar.val=indices p.queries begin1.val end1.val folded) ∧
  (∀ out cc1 cc2, p.backend.c1=some cc1 → p.backend.c2=some cc2 →
    out.length=(runs i).plan.offNodes →
    resultBytes (prover.append_node_slots out cc1 cc2 p.tree p.queries)=
      exceptBytes (ProverCommitPublish43.slots (runs i).plan.slots (bytes out.val)))

def PV_RJN_Link_PublishOrder {I : Type} (runs : I → Run) : Prop :=
  PV_RunJoin_PublishContext57.PV_RunJoin_Link_QueryAppend runs → PV_RJN_Link_NodeAppend runs →
  ∀ i (p : prover.Publication) (proof : alloc.vec.Vec U8), Fields (runs i) p → QueryRange p.queries → QueryContext (runs i) p →
    prover.publish_compact .S2 p=ok (.Ok proof) →
    ProverCommitPublish43.assembleLoop (.ok (front (runs i))) (runs i).plan.queries (runs i).plan.slots
      (runs i).plan.offNodes (runs i).plan.proofBytes=.ok (bytes proof.val)
#print axioms PV_RJN_Link_NodeAppend
#print axioms PV_RJN_Link_PublishOrder
end R1Z.PV_RJN_NodeContext

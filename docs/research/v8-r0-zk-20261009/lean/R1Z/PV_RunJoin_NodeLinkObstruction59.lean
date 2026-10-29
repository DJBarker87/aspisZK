import R1Z.PV_RunJoin_NodeNoSuccess59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeLinkObstruction59
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

def withCommitments (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment) :
    prover.Publication :=
  {p with backend := {p.backend with c1 := some cc1, c2 := some cc2}}

/-- The universal Fields-only node link cannot describe even one successful
node append: it equates that result and an unrelated empty-tree result to the
same fixed plan. No source execution or large tree is evaluated. -/
theorem complete {I : Type} (runs : I → Run) (i : I)
    (p : prover.Publication) (fields : Fields (runs i) p)
    (out next : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (length : out.length=(runs i).plan.offNodes)
    (depth : multiproof.LEAF_BITS=ok 18#u32)
    (success : prover.append_node_slots out cc1 cc2 p.tree p.queries=ok (.Ok next)) :
    ¬PV_RunJoin_Link_NodeAppend runs := by
  intro link
  have goodFields : Fields (runs i) (withCommitments p cc1 cc2) := fields
  have badFields : Fields (runs i)
      (withCommitments p (PV_RunJoin_NodeNoSuccess59.replaceTree cc1) cc2) := fields
  have good := (link i (withCommitments p cc1 cc2) goodFields).2.2
    out cc1 cc2 rfl rfl length
  have bad := (link i (withCommitments p (PV_RunJoin_NodeNoSuccess59.replaceTree cc1) cc2)
      badFields).2.2 out (PV_RunJoin_NodeNoSuccess59.replaceTree cc1) cc2 rfl rfl length
  change resultBytes (prover.append_node_slots out cc1 cc2 p.tree p.queries)=_ at good
  rw [success] at good
  change some (bytes next.val)=_ at good
  change resultBytes (prover.append_node_slots out (PV_RunJoin_NodeNoSuccess59.replaceTree cc1)
    cc2 p.tree p.queries)=_ at bad
  rw [PV_RunJoin_NodeNoSuccess59.bytes_none out cc1 cc2 p.tree p.queries depth] at bad
  have impossible := good.trans bad.symm
  cases impossible

#print axioms withCommitments
#print axioms complete
end R1Z.PV_RunJoin_NodeLinkObstruction59

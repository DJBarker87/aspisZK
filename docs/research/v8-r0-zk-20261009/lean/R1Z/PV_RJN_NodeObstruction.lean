import R1Z.PV_RJN_NodeInstalled
import R1Z.PV_RJN_PublishTrace
import R1Z.PV_RJN_Producers
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJN_NodeObstruction
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

def substituted (p : prover.Publication) : prover.Publication :=
  {p with queries := PV_RJN_NodeReject.badQueries}

theorem fields (r : Run) (p : prover.Publication) (h : Fields r p) : Fields r (substituted p) := h

/-- The unchanged NodeAppend quantifier relates both this successful native
node call and an invalid-query substitution to the SAME model slot list. -/
theorem incompatible {I : Type} (runs : I → Run)
    (laws : PV_RJN_NodeReject.PV_RJN_Producer_NodePrimitives)
    (node : PV_RunJoin_Link_NodeAppend runs) (i : I) (p : prover.Publication)
    (hfields : Fields (runs i) p) (out proof : alloc.vec.Vec U8)
    (cc1 cc2 : host_commitment.Commitment) (hc1 : p.backend.c1=some cc1)
    (hc2 : p.backend.c2=some cc2) (hlen : out.length=(runs i).plan.offNodes)
    (success : prover.append_node_slots out cc1 cc2 p.tree p.queries=ok (.Ok proof)) : False := by
  have good := (node i p hfields).2.2 out cc1 cc2 hc1 hc2 hlen
  rw [success] at good
  change some (bytes proof.val)=exceptBytes _ at good
  have hf := fields (runs i) p hfields
  have split : compact.SPLIT=10#usize := by unfold compact.SPLIT; rfl
  obtain ⟨idx,hidx,hv⟩ := (node i (substituted p) hf).2.1 0#usize compact.SPLIT false
    (by rw [split]; scalar_tac) (by rw [split]; scalar_tac)
  change idx.val.map UScalar.val=indices PV_RJN_NodeReject.badQueries 0 compact.SPLIT.val false at hv
  rw [split] at hv
  change idx.val.map UScalar.val=indices PV_RJN_NodeReject.badQueries 0 10 false at hv
  rw [PV_RJN_NodeReject.indices] at hv
  have failure := PV_RJN_NodeReject.source laws out cc1 cc2 p.tree idx hidx hv
  have bad := (node i (substituted p) hf).2.2 out cc1 cc2 hc1 hc2 hlen
  change resultBytes (prover.append_node_slots out cc1 cc2 p.tree PV_RJN_NodeReject.badQueries)=_ at bad
  rw [failure] at bad
  change none=exceptBytes _ at bad
  have impossible : some (bytes proof.val)=none := good.trans bad.symm
  cases impossible

/-- A successful source publication with the front association. This names
what an honest actual producer must supply; it contains no append or assembly
law and no NodeAppend conclusion. -/
def PV_RJN_Producer_Publication {I : Type} (runs : I → Run) : Prop :=
  ∃ (i : I) (p : prover.Publication) (proof : alloc.vec.Vec U8),
    Fields (runs i) p ∧ PV_RunJoin_PublishContext57.QueryContext (runs i) p ∧
    prover.publish_compact .S2 p=ok (.Ok proof)

theorem no_successful_witness {I : Type} (runs : I → Run)
    (laws : PV_RJN_NodeReject.PV_RJN_Producer_NodePrimitives)
    (layout : PV_RJN_Producers.PV_RJN_Producer_Layout runs)
    (producer : PV_RJN_Producer_Publication runs) : ¬PV_RunJoin_Link_NodeAppend runs := by
  intro node
  obtain ⟨i,p,proof,hfields,hcontext,success⟩ := producer
  obtain ⟨size,openings,nodes,magic,tag,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,ib,cc1,cc2,
    semanticResult,valuesResult,hsize,hmagic,htag,hh0,hh1,hsem,hclaim,hib,hh4,hh5,hh6,hh7,hh8,
    hopen,hopenlen,hc1,hc2,hh9,hnodes,hnodelen,hn,hprooflen⟩ := PV_RJN_PublishTrace.source .S2 p proof success
  obtain ⟨sz,op,nd,mg,tg,hsz,hop,hnd,hmg,htg,hpsize,hpop,hpnd,hheader⟩ := layout i
  have he := Result.ok.inj (hnd.symm.trans hnodes)
  subst nd
  have hlen : h9.length=(runs i).plan.offNodes := by
    rw [hpnd]
    exact congrArg UScalar.val hnodelen
  exact incompatible runs laws node i p hfields h9 proof cc1 cc2 hc1 hc2 hlen hn

#print axioms fields
#print axioms incompatible
#print axioms PV_RJN_Producer_Publication
#print axioms no_successful_witness
end R1Z.PV_RJN_NodeObstruction

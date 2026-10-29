import R1Z.PV_RunJoin_QueryIndexInstalled56
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLinkObstruction56
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

/-- The fixed Fields predicate does not constrain the backend or queries. -/
def poison (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment) : prover.Publication :=
  {p with backend:={p.backend with c1:=some cc1,c2:=some cc2},
    queries:=PV_RunJoin_QueryInvalidIndex56.badQueries}

theorem fields (r : Run) (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hf : Fields r p) : Fields r (poison p cc1 cc2) := hf

/-- Explicit source counterexample to the unguarded QueryAppend link whenever
    its front fields and output offset have an instance. -/
theorem impossible {I : Type} (runs : I → Run) (i : I) (p : prover.Publication)
    (cc1 cc2 : host_commitment.Commitment) (out : alloc.vec.Vec U8)
    (hf : Fields (runs i) p) (hoff : out.length=(runs i).plan.offOpenings)
    (reject : aspis_core.r0.domain.FibreIndex.new 262144#usize=ok (.Err .IndexOutOfRange)) :
    ¬PV_RunJoin_Link_QueryAppend runs := by
  intro link
  have hfields := fields (runs i) p cc1 cc2 hf
  obtain ⟨next,success,_⟩ := (link i (poison p cc1 cc2) hfields).2 out cc1 cc2 rfl rfl hoff
  have failure := PV_RunJoin_QueryInvalidIndex56.source out cc1 cc2
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts reject
  change prover.append_query_openings out cc1 cc2 PV_RunJoin_QueryInvalidIndex56.badQueries
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next at success
  rw [failure] at success
  cases success

#print axioms poison
#print axioms fields
#print axioms impossible
end R1Z.PV_RunJoin_QueryLinkObstruction56

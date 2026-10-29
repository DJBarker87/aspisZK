import R1Z.PV_RJQ_FinishTrace
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FinishFrame63
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact retained source fields. No model arithmetic or serialization equality
is assumed; this is the successful source constructor's complete frame. -/
theorem complete (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)
    (p : prover.Publication) (success : prover.finish_opening variant hash prepared salts=ok (.Ok p)) :
    p.backend=prepared.backend ∧ p.semantic_bytes=prepared.sem.bytes ∧ p.y1=prepared.y1 ∧
      p.inactive=prepared.inactive ∧ p.c0bytes=prepared.c0bytes ∧
      p.folded_word=prepared.folded_word ∧ p.folded_salts=salts := by
  obtain ⟨leaves,o,tree,root,second,cbytes,payload0,payload,alpha,next,final,fbytes,queries,tr,
    hleaves,htree,ho,hroot,hsecond,hcbytes,hpayload0,hpayload,hscalar,hfinal,hfbytes,hqueries,hpublication⟩ :=
      PV_RJQ_FinishTrace.source variant hash prepared salts p success
  rw [hpublication]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms complete
end R1Z.PV_RunJoin_FinishFrame63

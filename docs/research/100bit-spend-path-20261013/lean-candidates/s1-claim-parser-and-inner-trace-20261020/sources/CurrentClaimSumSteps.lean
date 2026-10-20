import CurrentClaimSumModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim
open Concrete
abbrev Range := core.ops.range.Range Usize

def cell (a : Array E 7#usize) (j : Usize) (h : j.val<7) : E :=
  a.val[j.val]'(by rw [a.property]; exact h)

theorem sum_body_step (k parts : Array E 7#usize) (iter : Range) (claim : E)
    (hend : iter.end.val=7) (hlt : iter.start.val<7)
    (hk : Canonical (cell k iter.start hlt))
    (hp : Canonical (cell parts iter.start hlt)) (hc : Canonical claim) :
    ∃ iter' claim', verifier.prepared_claim_sum_loop.body k parts iter claim=.ok (.cont (iter',claim')) ∧
      iter'.start.val=iter.start.val+1 ∧ iter'.end=iter.end ∧ Canonical claim' ∧
      decode claim'=decode claim+decode (cell k iter.start hlt)*decode (cell parts iter.start hlt) := by
  obtain ⟨pair,hnext,hs⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter (by omega))
  rcases pair with ⟨opt,iter'⟩
  rcases hs with ⟨hopt,hstart,hend'⟩
  subst opt
  obtain ⟨kv,hkv,hkvval⟩ := WP.spec_imp_exists
    (Array.index_usize_spec k iter.start (by simpa [k.property] using hlt))
  obtain ⟨pv,hpv,hpvval⟩ := WP.spec_imp_exists
    (Array.index_usize_spec parts iter.start (by simpa [parts.property] using hlt))
  have hkve : kv=cell k iter.start hlt := by simpa [cell] using hkvval
  have hpve : pv=cell parts iter.start hlt := by simpa [cell] using hpvval
  subst kv; subst pv
  obtain ⟨prod,hm,hmc,hme⟩ := mul_total_exact (cell k iter.start hlt) (cell parts iter.start hlt) hk hp
  obtain ⟨out,ha,hac,hae⟩ := add_total_exact claim prod hc hmc
  refine ⟨iter',out,?_,hstart,hend',hac,?_⟩
  · rw [verifier.prepared_claim_sum_loop.body,hnext,bind_tc_ok]
    change ((do
      let pv ← Array.index_usize parts iter.start
      trace.value 14#u16 iter.start pv
      let kv ← Array.index_usize k iter.start
      let pr ← aspis_core.field.WideExact.mul kv pv
      let cl ← aspis_core.field.WideExact.add claim pr
      ok (.cont (iter',cl))) : Result (ControlFlow (Range × E) E)) = .ok (.cont (iter',out))
    simp only [hpv,hkv,trace.value,bind_tc_ok,hkve,hpve,hm,ha]
  · rw [hae,hme]

theorem sum_body_done (k parts : Array E 7#usize) (iter : Range) (claim : E)
    (hge : iter.end.val ≤ iter.start.val) :
    verifier.prepared_claim_sum_loop.body k parts iter claim = .ok (.done claim) := by
  obtain ⟨pair,hnext,hs⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize) (by intros; rfl) iter hge)
  rcases pair with ⟨opt,iter'⟩
  rcases hs with ⟨hopt,_⟩
  subst opt
  rw [verifier.prepared_claim_sum_loop.body,hnext,bind_tc_ok]
  rfl
#print axioms sum_body_step
#print axioms sum_body_done
end AspisR1CurrentPreparedClaim

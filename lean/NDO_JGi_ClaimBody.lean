import NDO_JGi_Parts
set_option autoImplicit false
namespace AspisR1.JGi_ClaimBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentPreparedClaim Concrete
open JGi_DotOps (ops CanonQ)
open JGi_Parts

theorem step {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (k parts : Array E 7#usize)
    (iter : ClaimScalar.Range) (hend : iter.end.val=6) (hi : iter.start.val<6)
    (hc : CanonicalArray parts)
    (dots : ∀ point : Usize,point.val<6 → ∃ out,
      verifier.prepared_claim_dot ops D sem y1 g point=ok (.Ok out) ∧ Canonical out) :
    ∃ iter' parts',verifier.prepared_claim_loop.body ops D sem y1 g k iter parts=ok (.cont (iter',parts')) ∧
      iter'.start.val=iter.start.val+1 ∧ iter'.end.val=6 ∧ CanonicalArray parts' := by
  obtain ⟨pair,next,meaning⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros;rfl) (by intros;rfl) iter (by omega))
  rcases pair with ⟨opt,iter'⟩
  rcases meaning with ⟨ho,hs,he⟩
  subst opt
  obtain ⟨out,dot,canonical⟩ := dots iter.start hi
  obtain ⟨i,add,hadd⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=iter.start) (y:=1#usize) (by scalar_tac))
  obtain ⟨parts',write,hparts⟩ := update parts i out (by scalar_tac) hc canonical
  refine ⟨iter',parts',?_,hs,by rw [he];exact hend,hparts⟩
  unfold verifier.prepared_claim_loop.body
  simp only [next,bind_tc_ok,Aeneas.Std.uncurry,dot,
    core.result.Result.Insts.CoreOpsTry.branch,add,write]
#print axioms step

theorem done {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (k parts : Array E 7#usize)
    (iter : ClaimScalar.Range) (hend : iter.end.val=6) (hi : iter.start.val=6)
    (hk : CanonicalArray k) (hp : CanonicalArray parts) :
    ∃ out,verifier.prepared_claim_loop.body ops D sem y1 g k iter parts=ok (.done (.Ok out)) ∧ Canonical out := by
  obtain ⟨pair,next,meaning⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros;rfl) iter (by omega))
  rcases pair with ⟨opt,iter'⟩
  rcases meaning with ⟨ho,hs⟩
  subst opt
  obtain ⟨out,call,canonical,meaning⟩ := prepared_claim_sum_total_exact k parts hk hp
  refine ⟨out,?_,canonical⟩
  unfold verifier.prepared_claim_loop.body
  rw [next,bind_tc_ok,call,bind_tc_ok]
  rfl
#print axioms done
end AspisR1.JGi_ClaimBody

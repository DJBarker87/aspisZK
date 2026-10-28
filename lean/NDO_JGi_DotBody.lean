import NDO_JGi_DotOps
import CurrentClaimScalarBody
set_option autoImplicit false
namespace AspisR1.JGi_DotBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentPreparedClaim
open JGi_DotOps

theorem step {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (iter : ClaimScalar.Range)
    (dot : State) (hend : iter.end.val=29) (hi : iter.start.val<29)
    (hc : dot.count.val=iter.start.val)
    (read : ∀ l : Usize,l.val<29 → ∃ q,ClaimScalar.read ops sem y1 point l=ok q ∧ CanonQ q)
    (weights : ∀ l : Usize,l.val<29 → ∃ x,Array.index_usize g l=ok x ∧ Concrete.Canonical x) :
    ∃ iter' dot',verifier.prepared_claim_dot_loop.body ops D y1 g iter sem point dot=
      ok (.cont (iter',sem,point,dot')) ∧
      iter'.start.val=iter.start.val+1 ∧ iter'.end.val=29 ∧ dot'.count.val=iter'.start.val := by
  obtain ⟨pair,next,meaning⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros;rfl) (by intros;rfl) iter (by omega))
  rcases pair with ⟨opt,iter'⟩
  rcases meaning with ⟨ho,hs,he⟩
  subst opt
  obtain ⟨q,rq,cq⟩ := read iter.start hi
  obtain ⟨x,rx,cx⟩ := weights iter.start hi
  obtain ⟨dot',push,count⟩ := JGi_DotOps.push dot x q cx cq (by omega)
  refine ⟨iter',dot',?_,hs,by rw [he];exact hend,by omega⟩
  rw [ClaimScalar.body_eq_source]
  unfold ClaimScalar.body
  rw [next,bind_tc_ok]
  simp only [rq,rx,push,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]

#print axioms step

theorem done {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (iter : ClaimScalar.Range)
    (dot : State) (hend : iter.end.val=29) (hi : iter.start.val=29) :
    ∃ out,verifier.prepared_claim_dot_loop.body ops D y1 g iter sem point dot=
      ok (.done (.Ok out)) ∧ Concrete.Canonical out := by
  obtain ⟨pair,next,meaning⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros;rfl) iter (by omega))
  rcases pair with ⟨opt,iter'⟩
  rcases meaning with ⟨ho,hs⟩
  subst opt
  obtain ⟨out,finish,canonical⟩ := JGi_DotOps.finish dot
  refine ⟨out,?_,canonical⟩
  rw [ClaimScalar.body_eq_source]
  unfold ClaimScalar.body
  rw [next,bind_tc_ok,finish,bind_tc_ok]
#print axioms done
end AspisR1.JGi_DotBody

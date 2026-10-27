import XSa_DotBody
import XSa_LoopErrors
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_DotLoop
open AspisR1ClaimPreparedBridge

theorem paired {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g)
 (point : Nat) (hp : point<6) (n : Nat) (iter : Range) (a b : Dot)
 (hend : iter.end.val=29) (remaining : iter.start.val+n=29) :
 mapR outcome (run sem s g point n iter.start a b) =
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop ops D
   iter (toClaimSem sem) s (arr toClaimE g) (XRn_Join_usize point) (state a b iter.start) := by
 induction n generalizing iter a b with
 | zero => exact XSa_DotDone.done D sem s g point iter a b (by omega)
 | succ n ih =>
   have hi : iter.start.val<29 := by omega
   obtain ⟨pair,hn,hs⟩ := WP.spec_imp_exists
     (core.iter.range.IteratorRange.next_UScalar_some_spec
       (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
       (by intros; rfl) (by intros; rfl) iter (by omega))
   rcases pair with ⟨opt,iter'⟩
   rcases hs with ⟨ho,his,hie⟩
   subst opt
   have hb := XSa_DotBody.body D sem s g hg point hp iter iter' hi a b hn
   cases hr : XRy_ClaimSelect.read (es sem) s point iter.start.val with
   | fail e =>
     simp only [run,hr,bind_tc_fail,map_fail]
     symm
     apply XSa_LoopErrors.failed
     change AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop.body ops D s (arr toClaimE g)
       iter (toClaimSem sem) (XRn_Join_usize point) (state a b iter.start) = fail e
     rw [hb,hr,bind_tc_fail]
   | div =>
     simp only [run,hr,bind_tc_div,map_div]
     symm
     apply XSa_LoopErrors.diverged
     change AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop.body ops D s (arr toClaimE g)
       iter (toClaimSem sem) (XRn_Join_usize point) (state a b iter.start) = div
     rw [hb,hr,bind_tc_div]
   | ok q =>
     by_cases hq : XSa_CheckedQ.valid q=true
     · obtain ⟨a',b',next,ra,rb,en,hnext,pt⟩ := XSa_DotPushPair.paired a b iter.start hi
         (cell g iter.start hi) (hg _ hi) q hq
       have he : next=iter'.start := UScalar.eq_of_val_eq (hnext.trans his.symm)
       have hc : AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop.body ops D s (arr toClaimE g)
         iter (toClaimSem sem) (XRn_Join_usize point) (state a b iter.start) =
         ok (.cont (iter',toClaimSem sem,XRn_Join_usize point,state a' b' iter'.start)) := by
         rw [hb,hr,bind_tc_ok,pt,bind_tc_ok,he]
         rfl
       simp only [run,hr,bind_tc_ok,hq,if_true,(coefficient g hg iter.start hi).1,ra,rb,en,he]
       exact (ih iter' a' b' (by rw [hie]; exact hend) (by omega)).trans
         (XRy_PowersLoop.cont _ _ _ hc).symm
     · have hfalse : XSa_CheckedQ.valid q=false := Bool.eq_false_iff.mpr hq
       have pt := XSa_DotReject.reject a b iter.start hi (cell g iter.start hi) q hfalse
       simp only [run,hr,bind_tc_ok,hq,if_false,map_ok]
       symm
       apply XRy_PowersLoop.done
       change AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop.body ops D s (arr toClaimE g)
         iter (toClaimSem sem) (XRn_Join_usize point) (state a b iter.start) = _
       rw [hb,hr,bind_tc_ok,pt,bind_tc_ok]
       rfl

#print axioms paired
end XSa_DotLoop

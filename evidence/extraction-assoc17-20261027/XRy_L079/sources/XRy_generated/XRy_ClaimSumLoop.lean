import XRy_ClaimSumStep
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep
set_option autoImplicit false
namespace XRy_ClaimSumLoop
open AspisR1ClaimPreparedBridge

def run (k parts : Seven) : Nat → Usize → C.E → Result C.E
 | 0,_,sum => ok sum
 | n+1,i,sum => do
   let sum' ← step k parts sum i
   let j ← i+1#usize
   run k parts n j sum'

theorem paired (n : Nat) (k parts : Seven) (hk : canonical k) (hp : canonical parts)
 (iter : Range) (sum : C.E) (hs : XRy_WideMultiply.Canonical sum)
 (hend : iter.end.val=7) (remaining : iter.start.val+n=7) :
 ∃ out, XRy_WideMultiply.Canonical out ∧ run k parts n iter.start sum=ok out ∧
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum_loop
   iter (arr toClaimE k) (arr toClaimE parts) (toClaimE sum)=ok (toClaimE out) := by
 induction n generalizing iter sum with
 | zero =>
   refine ⟨sum,hs,rfl,?_⟩
   apply XRy_PowersLoop.done
   exact AspisR1CurrentPreparedClaim.sum_body_done _ _ iter (toClaimE sum) (by omega)
 | succ n ih =>
   obtain ⟨iter',next,er,hn,hstart,hend',et⟩ := XRy_ClaimSumStep.paired
     k parts iter sum hend (by omega) hk hp hs
   have hAdd : (iter.start+1#usize : Result Usize) ⦃ j => j.val=iter.start.val+1 ⦄ := by
     apply UScalar.add_spec
     scalar_tac
   obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists hAdd
   have he : j=iter'.start := UScalar.eq_of_val_eq (hj.trans hstart.symm)
   obtain ⟨out,ho,hr,ht⟩ := ih iter' next hn (by rw [hend']; exact hend) (by omega)
   refine ⟨out,ho,?_,?_⟩
   · rw [run,er,bind_tc_ok,ej,bind_tc_ok,he]
     exact hr
   · exact (XRy_PowersLoop.cont _ _ _ et).trans ht

#print axioms paired
end XRy_ClaimSumLoop

import XSa_DotRun
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_DotDone
open AspisR1ClaimPreparedBridge

theorem done {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat) (iter : Range) (a b : Dot)
 (hge : iter.end.val≤iter.start.val) :
 mapR outcome (run sem s g point 0 iter.start a b) =
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_dot_loop ops D s (arr toClaimE g)
   iter (toClaimSem sem) (XRn_Join_usize point) (state a b iter.start) := by
 obtain ⟨out,hr,hc,ht⟩ := XSa_FinishPair.paired a b iter.start
 obtain ⟨pair,hn,hs⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_none_spec
     (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
     (by intros; rfl) iter hge)
 rcases pair with ⟨opt,iter'⟩
 rcases hs with ⟨ho,_⟩
 subst opt
 rw [run,hr,bind_tc_ok,map_ok]
 symm
 apply XRy_PowersLoop.done
 rw [AspisR1CurrentPreparedClaim.ClaimScalar.body_eq_source]
 unfold AspisR1CurrentPreparedClaim.ClaimScalar.body
 rw [hn,bind_tc_ok,ht,bind_tc_ok]
 rfl

#print axioms done
end XSa_DotDone

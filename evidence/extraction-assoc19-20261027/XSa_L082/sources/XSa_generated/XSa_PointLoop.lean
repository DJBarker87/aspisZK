import XSa_PointRun
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PointLoop
open AspisR1ClaimPreparedBridge
abbrev Seven := XRy_ClaimSumStep.Seven

theorem paired {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (hg : canonical g)
 (k : Seven) (hk : XRy_ClaimSumStep.canonical k) (n : Nat) (iter : Range)
 (parts : Seven) (hp : XRy_ClaimSumStep.canonical parts)
 (hend : iter.end.val=6) (remaining : iter.start.val+n=6) :
 mapR outcome (XSa_PointRun.run sem s g k n iter.start parts) =
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop ops D iter (toClaimSem sem) s
   (arr toClaimE g) (arr toClaimE k) (arr toClaimE parts) := by
 induction n generalizing iter parts with
 | zero => exact XSa_PointRun.done D sem s g k parts hk hp iter (by omega)
 | succ n ih =>
   have hi : iter.start.val<6 := by omega
   obtain ⟨pair,hn,hs⟩ := WP.spec_imp_exists
     (core.iter.range.IteratorRange.next_UScalar_some_spec
       (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
       (by intros; rfl) (by intros; rfl) iter (by omega))
   rcases pair with ⟨opt,iter'⟩
   rcases hs with ⟨ho,his,hie⟩
   subst opt
   have he : XRn_Join_usize iter.start.val=iter.start :=
     UScalar.eq_of_val_eq (XRy_ClaimSelect.usize_value iter.start.val (by omega))
   have hpart := XSa_PartAssociation.part D sem s g hg iter.start.val hi
   rw [he] at hpart
   cases hr : XRn_Join_preparedPart (es sem) s g iter.start.val with
   | fail e =>
     rw [hr,map_fail] at hpart
     simp only [XSa_PointRun.run,hr,bind_tc_fail,map_fail]
     symm
     apply XSa_LoopErrors.failed
     change AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body ops D (toClaimSem sem) s
       (arr toClaimE g) (arr toClaimE k) iter (arr toClaimE parts)=fail e
     rw [AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body,hn,bind_tc_ok]
     try dsimp only
     rw [←hpart,bind_tc_fail]
   | div =>
     rw [hr,map_div] at hpart
     simp only [XSa_PointRun.run,hr,bind_tc_div,map_div]
     symm
     apply XSa_LoopErrors.diverged
     change AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body ops D (toClaimSem sem) s
       (arr toClaimE g) (arr toClaimE k) iter (arr toClaimE parts)=div
     rw [AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body,hn,bind_tc_ok]
     try dsimp only
     rw [←hpart,bind_tc_div]
   | ok opt =>
     rw [hr,map_ok] at hpart
     cases opt with
     | none =>
       simp only [XSa_PointRun.run,hr,bind_tc_ok,map_ok]
       symm
       apply XRy_PowersLoop.done
       change AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body ops D (toClaimSem sem) s
         (arr toClaimE g) (arr toClaimE k) iter (arr toClaimE parts)=_
       rw [AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body,hn,bind_tc_ok]
       try dsimp only
       rw [←hpart]
       rfl
     | some v =>
       have hv := XSa_PartCanonical.canonical D sem s g hg iter.start.val hi v hr
       obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=iter.start) (y:=1#usize) (by scalar_tac))
       have hjv : j.val=iter.start.val+1 := by scalar_tac
       have hj7 : j.val<7 := by omega
       have heq : j=iter'.start := UScalar.eq_of_val_eq (hjv.trans his.symm)
       have eu := XSa_ArraySeven.update parts j v hj7
       have et : Array.update (arr toClaimE parts) j (toClaimE v)=ok (arr toClaimE (parts.set j v)) := by
         rw [XSa_ArraySeven.update _ _ _ hj7,←XRy_ArrayMap.set]
       have hc : AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body ops D (toClaimSem sem) s
         (arr toClaimE g) (arr toClaimE k) iter (arr toClaimE parts)=
         ok (.cont (iter',arr toClaimE (parts.set j v))) := by
         rw [AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body,hn,bind_tc_ok]
         try dsimp only
         rw [←hpart]
         change (do let next ← iter.start+1#usize
                    let out ← Array.update (arr toClaimE parts) next (toClaimE v)
                    ok (.cont (iter',out))) = _
         rw [ej,bind_tc_ok,et,bind_tc_ok]
       simp only [XSa_PointRun.run,hr,bind_tc_ok,ej,eu,heq]
       exact (ih iter' (parts.set iter'.start v)
         (XSa_ArraySeven.canonical_set parts hp iter'.start (by rw [←heq];exact hj7) v hv)
         (by rw [hie];exact hend) (by omega)).trans (XRy_PowersLoop.cont _ _ _ hc).symm

#print axioms paired
end XSa_PointLoop

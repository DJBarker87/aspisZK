import XSa_ArraySeven
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PointRun
open AspisR1ClaimPreparedBridge
abbrev Seven := XRy_ClaimSumStep.Seven

def run {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (k : Seven) :
 Nat → Usize → Seven → Result (Option C.E)
 | 0,_,parts => do
   let out ← (k.val.zip parts.val).foldlM XSa_ClaimPairs.addTerm XRy_Powers.zero
   ok (some out)
 | n+1,i,parts => do
   let part ← XRn_Join_preparedPart (es sem) s g i.val
   match part with
   | none => ok none
   | some value => do
     let j ← i+1#usize
     let next ← Array.update parts j value
     run sem s g k n j next

theorem done {H : Type} (D : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
 (sem : C.Sem H) (s : Slice U8) (g : Coeff) (k parts : Seven)
 (hk : XRy_ClaimSumStep.canonical k) (hp : XRy_ClaimSumStep.canonical parts)
 (iter : Range) (hge : iter.end.val ≤ iter.start.val) :
 mapR outcome (run sem s g k 0 iter.start parts) =
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop ops D iter (toClaimSem sem) s
   (arr toClaimE g) (arr toClaimE k) (arr toClaimE parts) := by
 obtain ⟨out,hc,hr,ht⟩ := XSa_ClaimSumJoin.paired k parts hk hp
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
 change AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body ops D (toClaimSem sem) s
   (arr toClaimE g) (arr toClaimE k) iter (arr toClaimE parts) = _
 rw [AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body,hn,bind_tc_ok]
 dsimp only
 rw [ht,bind_tc_ok]
 rfl

#print axioms done
end XSa_PointRun

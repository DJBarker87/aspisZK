import XRy_ArrayRead
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ClaimSumStep
open AspisR1ClaimPreparedBridge
abbrev Range := core.ops.range.Range Usize
abbrev Seven := Array C.E 7#usize

def cell (a : Seven) (i : Usize) (hi : i.val<7) : C.E :=
 a.val[i.val]'(by have hn : a.val.length=7 := a.property; omega)
def canonical (a : Seven) : Prop := ∀ i hi, XRy_WideMultiply.Canonical (cell a i hi)
def step (k parts : Seven) (sum : C.E) (i : Usize) : Result C.E := do
 let part ← Array.index_usize parts i
 let power ← Array.index_usize k i
 let term ← aspis_core.field.wide_exact.WideExact.mul power part
 aspis_core.field.wide_exact.WideExact.add sum term

theorem paired (k parts : Seven) (iter : Range) (sum : C.E)
 (hend : iter.end.val=7) (hlt : iter.start.val<7)
 (hk : canonical k) (hp : canonical parts) (hs : XRy_WideMultiply.Canonical sum) :
 ∃ iter' out, step k parts sum iter.start=ok out ∧ XRy_WideMultiply.Canonical out ∧
 iter'.start.val=iter.start.val+1 ∧ iter'.end=iter.end ∧
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum_loop.body
   (arr toClaimE k) (arr toClaimE parts) iter (toClaimE sum)=ok (.cont (iter',toClaimE out)) := by
 obtain ⟨pair,hn,hnv⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
     (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
     (by intros; rfl) (by intros; rfl) iter (by omega))
 rcases pair with ⟨opt,iter'⟩
 rcases hnv with ⟨ho,hi,he⟩
 subst opt
 have h7 : (7#usize).val=7 := by scalar_tac
 have hkread := XRy_ArrayRead.read k iter.start (by simpa only [h7] using hlt)
 have hpread := XRy_ArrayRead.read parts iter.start (by simpa only [h7] using hlt)
 have tkread := XRy_ArrayRead.mapped toClaimE k iter.start (by simpa only [h7] using hlt)
 have tpread := XRy_ArrayRead.mapped toClaimE parts iter.start (by simpa only [h7] using hlt)
 obtain ⟨term,et,ht,tt⟩ := XRy_ClaimArithmetic.multiply
   (cell k iter.start hlt) (cell parts iter.start hlt) (hk _ hlt) (hp _ hlt)
 obtain ⟨out,eo,hout,tout⟩ := XRy_ClaimAdd.add sum term hs ht
 refine ⟨iter',out,?_,hout,hi,he,?_⟩
 · simp only [step,hpread,hkread,bind_tc_ok]
   change (do
     let t ← aspis_core.field.wide_exact.WideExact.mul (cell k iter.start hlt) (cell parts iter.start hlt)
     aspis_core.field.wide_exact.WideExact.add sum t) = _
   rw [et,bind_tc_ok,eo]
 · rw [AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum_loop.body,hn,bind_tc_ok]
   simp only [tpread,tkread,AspisR1CurrentPreparedClaim.trace.value,bind_tc_ok]
   change (do
     let pv ← Array.index_usize (arr toClaimE parts) iter.start
     let kv ← Array.index_usize (arr toClaimE k) iter.start
     let t ← AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul kv pv
     let o ← AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add (toClaimE sum) t
     ok (ControlFlow.cont (iter',o) : ControlFlow (Range × AspisR1CurrentPreparedClaim.Concrete.E) AspisR1CurrentPreparedClaim.Concrete.E)) = _
   simp only [tpread,tkread,bind_tc_ok]
   change (do
     let t ← AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul
       (toClaimE (cell k iter.start hlt)) (toClaimE (cell parts iter.start hlt))
     let o ← AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add (toClaimE sum) t
     ok (ControlFlow.cont (iter',o) : ControlFlow (Range × AspisR1CurrentPreparedClaim.Concrete.E) AspisR1CurrentPreparedClaim.Concrete.E)) = _
   rw [tt,bind_tc_ok,tout,bind_tc_ok]

#print axioms paired
end XRy_ClaimSumStep

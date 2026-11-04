import NGU_Powers
import NGU_ArrayRead
import NGU_Loop
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_WeightedStep
open Aeneas Aeneas.Std Result ControlFlow NFN_LPi_FieldValues NGU_Carriers
open AspisR1CurrentPreparedClaim
abbrev Range := core.ops.range.Range Usize
abbrev Seven := Array NE 7#usize
def canonical (a : Seven) : Prop := ∀ z ∈ a.val, canonE z

def step (k parts : Seven) (sum : NE) (i : Usize) : Result NE := do
 let part ← Array.index_usize parts i
 let power ← Array.index_usize k i
 let term ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul power part
 FIo_Native.aspis_core.field.wide_exact.WideExact.add sum term

/-- One arbitrary invariant prestate, same operands and ordered product/add.
The product value law is Lean-only; no Kani multiplication. -/
theorem paired (k parts : Seven) (iter : Range) (sum : NE)
 (hend : iter.end.val=7) (hlt : iter.start.val<7)
 (hk : canonical k) (hp : canonical parts) (hs : canonE sum) :
 ∃ iter' out, step k parts sum iter.start=ok out ∧ canonE out ∧
 iter'.start.val=iter.start.val+1 ∧ iter'.end=iter.end ∧
 verifier.prepared_claim_sum_loop.body
  (arr NGU_Powers.claim k) (arr NGU_Powers.claim parts) iter (NGU_Powers.claim sum)=
    ok (.cont (iter',NGU_Powers.claim out)) := by
 obtain ⟨pair,hn,hnv⟩ := WP.spec_imp_exists
  (core.iter.range.IteratorRange.next_UScalar_some_spec
    (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter (by omega))
 rcases pair with ⟨opt,iter'⟩
 rcases hnv with ⟨ho,hi,he⟩
 subst opt
 have ik : iter.start.val<k.val.length := by rw [k.property];exact hlt
 have ip : iter.start.val<parts.val.length := by rw [parts.property];exact hlt
 obtain ⟨term,et,ct,tt⟩ := NGU_ClaimOps.multiply k.val[iter.start.val] parts.val[iter.start.val]
  (hk _ (List.getElem_mem ik)) (hp _ (List.getElem_mem ip))
 obtain ⟨out,eo,co,to⟩ := NGU_ClaimOps.add sum term hs ct
 have kr := NGU_ArrayRead.read k iter.start hlt
 have pr := NGU_ArrayRead.read parts iter.start hlt
 have km := NGU_ArrayRead.mapped NGU_Powers.claim k iter.start hlt
 have pm := NGU_ArrayRead.mapped NGU_Powers.claim parts iter.start hlt
 refine ⟨iter',out,?_,co,hi,he,?_⟩
 · simp only [step,pr,kr,bind_tc_ok,et,eo]
 · rw [verifier.prepared_claim_sum_loop.body,hn,bind_tc_ok]
   simp only [pm,km,trace.value,bind_tc_ok,tt,to]

#print axioms paired
end AspisR1.NGU_WeightedStep
end

import S9ConstructorV3StatementLoopsCanonicalV1
import Aeneas.Std.RangeIter
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1S9StatementSourceLoopFactsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3

/-- No successful forward iterator None occurs before the source end. -/
theorem next_none_stop (iter iterNext : R)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (none,iterNext)) :
    iter.end.val≤iter.start.val := by
  by_contra hge
  obtain ⟨pair,hcall,hpost⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter (by omega))
  rcases pair with ⟨opt,next⟩
  rcases hpost with ⟨ho,hs,he⟩
  rw [hnext] at hcall
  have hp : (none,iterNext)=(opt,next) := Result.ok.inj hcall
  have ho' : (none : Option Usize)=opt := congrArg Prod.fst hp
  rw [←ho'] at ho
  cases ho

def statementTail (points : StatementPoints) (k d : Usize) (iter1 : R)
    (factors : Factors) : Result (ControlFlow (R × Factors) Factors) := do
  let i ← Array.index_usize TAU d
  let i1 ← lift (Std.Usize.wrapping_mul 2#usize i)
  let i2 ← lift (Std.Usize.wrapping_sub 9#usize i1)
  let a ← Array.index_usize points k
  let a1 ← Array.index_usize a i2
  let i3 ← lift (Std.Usize.wrapping_mul 2#usize i)
  let i4 ← lift (Std.Usize.wrapping_sub 8#usize i3)
  let b ← Array.index_usize a i4
  let q ← field.QM31.sub field.QM31.ONE a1
  let q1 ← field.QM31.sub field.QM31.ONE b
  let q2 ← field.QM31.mul q q1
  let q3 ← field.QM31.mul a1 q1
  let q4 ← field.QM31.mul q b
  let q5 ← field.QM31.mul a1 b
  let (old, back) ← Array.index_mut_usize factors k
  let rowOut ← Array.update old d (Array.make 4#usize [q2,q3,q4,q5] : Cell)
  ok (.cont (iter1, back rowOut))

theorem statementTail_success_cont
    (points : StatementPoints) (k d : Usize) (iter1 : R) (factors : Factors)
    (cf : ControlFlow (R × Factors) Factors)
    (h : statementTail points k d iter1 factors = .ok cf) :
    ∃ out, cf = .cont (iter1, out) := by
  unfold statementTail at h
  obtain ⟨v1, h1, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v2, h2, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v3, h3, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v4, h4, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v5, h5, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v6, h6, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v7, h7, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v8, h8, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v9, h9, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v10, h10, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v11, h11, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v12, h12, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v13, h13, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨v14, h14, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨pair, hmut, h⟩ := bind_success_inv _ _ _ h
  rcases pair with ⟨old, back⟩
  change (do
    let rowOut ← Array.update old d (Array.make 4#usize [v11,v12,v13,v14] : Cell)
    ok (ControlFlow.cont (iter1, back rowOut) : ControlFlow (R × Factors) Factors)) = .ok cf at h
  obtain ⟨rowOut, hupdate, h⟩ := bind_success_inv _ _ _ h
  exact ⟨back rowOut, (Result.ok.inj h).symm⟩

theorem inner_cont_has_next
    (points : StatementPoints) (k : Usize) (iter iterNext : R) (factors factorsOut : Factors)
    (hbody : weights_new_loop0_loop0.body points k iter factors = .ok (.cont (iterNext,factorsOut))) :
    ∃ d, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some d,iterNext) := by
  unfold weights_new_loop0_loop0.body at hbody
  obtain ⟨next,hnext,hrest⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.cont (iterNext,factorsOut) : ControlFlow (R × Factors) Factors) at hrest
    cases hrest
  | some d =>
    change statementTail points k d iter1 factors = .ok (.cont (iterNext,factorsOut)) at hrest
    obtain ⟨out,hcf⟩ := statementTail_success_cont points k d iter1 factors _ hrest
    have hiter : iterNext = iter1 := congrArg Prod.fst (ControlFlow.cont.inj hcf)
    subst iter1
    exact ⟨d,hnext⟩

theorem inner_done_same_factors
    (points : StatementPoints) (k : Usize) (iter : R) (factors out : Factors)
    (hbody : weights_new_loop0_loop0.body points k iter factors = .ok (.done out)) : out=factors := by
  unfold weights_new_loop0_loop0.body at hbody
  obtain ⟨next,hnext,hrest⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.done out : ControlFlow (R × Factors) Factors) at hrest
    exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some d =>
    change statementTail points k d iter1 factors = .ok (.done out) at hrest
    obtain ⟨out',hcf⟩ := statementTail_success_cont points k d iter1 factors _ hrest
    cases hcf

theorem outer_cont_has_execution
    (points : StatementPoints) (iter iterNext : R) (factors factorsOut : Factors)
    (hbody : weights_new_loop0.body points iter factors = .ok (.cont (iterNext,factorsOut))) :
    ∃ k, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some k,iterNext) ∧
      weights_new_loop0_loop0 {start:=0#usize, «end»:=5#usize} points factors k = .ok factorsOut := by
  unfold weights_new_loop0.body at hbody
  obtain ⟨next,hnext,hbody⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.cont (iterNext,factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    cases hbody
  | some k =>
    obtain ⟨factors1,hinner,hbody⟩ := bind_success_inv _ _ _ hbody
    have hstate := ControlFlow.cont.inj (Result.ok.inj hbody)
    have hi : iter1=iterNext := congrArg Prod.fst hstate
    have hf : factors1=factorsOut := congrArg Prod.snd hstate
    subst iterNext
    subst factorsOut
    exact ⟨k,hnext,hinner⟩

theorem outer_done_same_factors
    (points : StatementPoints) (iter : R) (factors out : Factors)
    (hbody : weights_new_loop0.body points iter factors = .ok (.done out)) : out=factors := by
  unfold weights_new_loop0.body at hbody
  obtain ⟨next,hnext,hbody⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.done out : ControlFlow (R × Factors) Factors) at hbody
    exact (ControlFlow.done.inj (Result.ok.inj hbody)).symm
  | some k =>
    obtain ⟨factors1,hinner,hbody⟩ := bind_success_inv _ _ _ hbody
    cases hbody


/-- Exact state and stop geometry from the SAME successful statement done branch. -/
theorem inner_done_state_stop
    (points : StatementPoints) (k : Usize) (iter : R) (factors out : Factors)
    (hbody : weights_new_loop0_loop0.body points k iter factors=.ok (.done out)) :
    out=factors ∧ iter.end.val≤iter.start.val := by
  have hout := inner_done_same_factors points k iter factors out hbody
  refine ⟨hout,?_⟩
  unfold weights_new_loop0_loop0.body at hbody
  obtain ⟨next,hnext,hrest⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,it⟩
  cases opt with
  | none => exact next_none_stop iter it hnext
  | some d =>
    change statementTail points k d it factors=.ok (.done out) at hrest
    obtain ⟨out',hc⟩ := statementTail_success_cont points k d it factors _ hrest
    cases hc

theorem outer_done_state_stop
    (points : StatementPoints) (iter : R) (factors out : Factors)
    (hbody : weights_new_loop0.body points iter factors=.ok (.done out)) :
    out=factors ∧ iter.end.val≤iter.start.val := by
  have hout := outer_done_same_factors points iter factors out hbody
  refine ⟨hout,?_⟩
  unfold weights_new_loop0.body at hbody
  obtain ⟨next,hnext,hrest⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,it⟩
  cases opt with
  | none => exact next_none_stop iter it hnext
  | some k =>
    obtain ⟨factors1,hi,hrest⟩ := bind_success_inv _ _ _ hrest
    cases hrest

#print axioms next_none_stop
#print axioms inner_cont_has_next
#print axioms inner_done_state_stop
#print axioms outer_cont_has_execution
#print axioms outer_done_state_stop
end AspisR1S9StatementSourceLoopFactsV1

import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3StatementCellCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3StatementLoopsCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3

private def statementTail (points : StatementPoints) (k d : Usize) (iter1 : R)
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

private theorem statementTail_success_cont
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

private theorem inner_cont_has_next
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

private theorem inner_done_same_factors
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

private def rangeMeasure (state : R × Factors) : Nat := state.1.end.val-state.1.start.val
private def factorInvariant (state : R × Factors) : Prop := FactorsCanonical state.2
private def statementInnerStep (points : StatementPoints) (k : Usize) (state : R × Factors) :
    Result (ControlFlow (R × Factors) Factors) := weights_new_loop0_loop0.body points k state.1 state.2

theorem statement_inner_loop_success_canonical
    (points : StatementPoints) (k : Usize) (iter : R) (factors out : Factors)
    (hp : StatementPointsCanonical points) (hf : FactorsCanonical factors)
    (hloop : weights_new_loop0_loop0 iter points factors k = .ok out) : FactorsCanonical out := by
  let step := statementInnerStep points k
  have hdone : ∀ s out, factorInvariant s → step s = .ok (.done out) → FactorsCanonical out := by
    rintro ⟨iter,factors⟩ out hs hstep
    have he := inner_done_same_factors points k iter factors out hstep
    subst out
    exact hs
  have hcont : ∀ s s', factorInvariant s → step s = .ok (.cont s') → factorInvariant s' := by
    rintro ⟨iter,factors⟩ ⟨iterNext,factorsNext⟩ hs hstep
    exact statement_cell_body_success_canonical points k iter iterNext factors factorsNext hp hs hstep
  have hdec : ∀ s s', step s = .ok (.cont s') → rangeMeasure s' < rangeMeasure s := by
    rintro ⟨iter,factors⟩ ⟨iterNext,factorsNext⟩ hstep
    obtain ⟨d,hnext⟩ := inner_cont_has_next points k iter iterNext factors factorsNext hstep
    obtain ⟨hlt,hd,hstart,hend⟩ := next_some_progress iter iterNext d hnext
    simp only [rangeMeasure,hstart,hend]
    omega
  have hloop' : Aeneas.Std.loop step (iter,factors) = .ok out := by
    change Aeneas.Std.loop (statementInnerStep points k) (iter,factors) = .ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step rangeMeasure factorInvariant FactorsCanonical hdone hcont hdec (iter,factors) out hf hloop'

private theorem outer_cont_has_execution
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

private theorem outer_done_same_factors
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

private def statementOuterStep (points : StatementPoints) (state : R × Factors) :
    Result (ControlFlow (R × Factors) Factors) := weights_new_loop0.body points state.1 state.2

/-- The entire first constructor phase preserves canonical factors. -/
theorem statement_outer_loop_success_canonical
    (points : StatementPoints) (iter : R) (factors out : Factors)
    (hp : StatementPointsCanonical points) (hf : FactorsCanonical factors)
    (hloop : weights_new_loop0 iter points factors = .ok out) : FactorsCanonical out := by
  let step := statementOuterStep points
  have hdone : ∀ s out, factorInvariant s → step s = .ok (.done out) → FactorsCanonical out := by
    rintro ⟨iter,factors⟩ out hs hstep
    have he := outer_done_same_factors points iter factors out hstep
    subst out
    exact hs
  have hcont : ∀ s s', factorInvariant s → step s = .ok (.cont s') → factorInvariant s' := by
    rintro ⟨iter,factors⟩ ⟨iterNext,factorsNext⟩ hs hstep
    obtain ⟨k,hnext,hinner⟩ := outer_cont_has_execution points iter iterNext factors factorsNext hstep
    exact statement_inner_loop_success_canonical points k {start:=0#usize, «end»:=5#usize}
      factors factorsNext hp hs hinner
  have hdec : ∀ s s', step s = .ok (.cont s') → rangeMeasure s' < rangeMeasure s := by
    rintro ⟨iter,factors⟩ ⟨iterNext,factorsNext⟩ hstep
    obtain ⟨k,hnext,hinner⟩ := outer_cont_has_execution points iter iterNext factors factorsNext hstep
    obtain ⟨hlt,hd,hstart,hend⟩ := next_some_progress iter iterNext k hnext
    simp only [rangeMeasure,hstart,hend]
    omega
  have hloop' : Aeneas.Std.loop step (iter,factors) = .ok out := by
    change Aeneas.Std.loop (statementOuterStep points) (iter,factors) = .ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step rangeMeasure factorInvariant FactorsCanonical hdone hcont hdec (iter,factors) out hf hloop'

#print axioms statement_inner_loop_success_canonical
#print axioms statement_outer_loop_success_canonical
end AspisR1S9ConstructorV3StatementLoopsCanonicalV1

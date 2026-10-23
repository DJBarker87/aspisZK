import S9ConstructorV3Loop2InnerCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1S9ConstructorV3CircleControlV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
/- Public source-flow interfaces copied from the retained private canonical
proofs in S9ConstructorV3Loop2InnerCanonicalV1. No new source model or
arithmetic premise is introduced; the original successful source spans and
same tail are retained to support full decoded-value loop invariants. -/
/-- Exact continuation of the generated body after its `some d` range result. -/
def cellTail (k d : Std.Usize) (iter1 : R) (factors : Factors) (x : Q) :
    Result (ControlFlow (R × Factors × Q) Factors) := do
  let y ← AspisR1S9ActualWeightsNewBoxNewV3.double x
  let q ← AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y
  let i ← lift (Std.Usize.wrapping_add 3#usize k)
  let (old, back) ← Array.index_mut_usize factors i
  let rowOut ← Array.update old d
    (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q] : Cell)
  let xNext ← AspisR1S9ActualWeightsNewBoxNewV3.double y
  ok (.cont (iter1, back rowOut, xNext))

theorem cellTail_success_cont
    (k d : Std.Usize) (iter1 : R) (factors : Factors) (x : Q)
    (cf : ControlFlow (R × Factors × Q) Factors)
    (h : cellTail k d iter1 factors x = .ok cf) :
    ∃ factorsOut xOut, cf = .cont (iter1, factorsOut, xOut) := by
  unfold cellTail at h
  obtain ⟨y, hy, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨q, hq, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨mutPair, hm, h⟩ := bind_success_inv _ _ _ h
  rcases mutPair with ⟨old, back⟩
  change (do
    let rowOut ← Array.update old d
      (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q] : Cell)
    let xNext ← AspisR1S9ActualWeightsNewBoxNewV3.double y
    ok (ControlFlow.cont (iter1, back rowOut, xNext) : ControlFlow (R × Factors × Q) Factors)) = ok cf at h
  obtain ⟨rowOut, hu, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨xNext, hxNext, h⟩ := bind_success_inv _ _ _ h
  exact ⟨back rowOut, xNext, (Result.ok.inj h).symm⟩

theorem body_cont_has_next
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q)
    (iterNext : R) (factorsNext : Factors) (xNext : Q)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.cont (iterNext, factorsNext, xNext))) :
    ∃ d, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some d, iterNext) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases pair with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors × Q) Factors) =
      ok (ControlFlow.cont (iterNext, factorsNext, xNext) : ControlFlow (R × Factors × Q) Factors) at hrest
    cases hrest
  | some d =>
    change cellTail k d iter1 factors x = ok (.cont (iterNext, factorsNext, xNext)) at hrest
    obtain ⟨factorsOut, xOut, hcf⟩ := cellTail_success_cont
      k d iter1 factors x _ hrest
    have hiter : iterNext = iter1 := congrArg Prod.fst (ControlFlow.cont.inj hcf)
    subst iter1
    exact ⟨d, hnext⟩

theorem body_done_same_factors
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q) (out : Factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.done out)) : out = factors := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases pair with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors × Q) Factors) =
      ok (ControlFlow.done out : ControlFlow (R × Factors × Q) Factors) at hrest
    exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some d =>
    change cellTail k d iter1 factors x = ok (.done out) at hrest
    obtain ⟨factorsOut, xOut, hcf⟩ := cellTail_success_cont
      k d iter1 factors x _ hrest
    cases hcf

/-- Successful source loop termination supplies actual range exhaustion. -/
theorem body_done_has_next_none
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q) (out : Factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.done out)) :
    ∃ iterNext, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none,iterNext) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  obtain ⟨pair,hnext,hrest⟩ := bind_success_inv _ _ _ hbody
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none => exact ⟨iter1,hnext⟩
  | some d =>
    change cellTail k d iter1 factors x = .ok (.done out) at hrest
    obtain ⟨factorsOut,xOut,hcf⟩ := cellTail_success_cont k d iter1 factors x _ hrest
    cases hcf

#print axioms cellTail_success_cont
#print axioms body_cont_has_next
#print axioms body_done_same_factors
#print axioms body_done_has_next_none
end AspisR1S9ConstructorV3CircleControlV1

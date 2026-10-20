import CurrentClaimOuterBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimTrace
open Concrete

theorem next_some_step (iter iter' : Range) (point : Usize)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some point,iter')) :
    point=iter.start ∧ iter.start.val < iter.end.val ∧
      iter'.start.val=iter.start.val+1 ∧ iter'.end=iter.end := by
  have hs := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter
  rw [h,WP.spec_ok] at hs
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt,↓reduceIte] at hs
    rcases hs with ⟨⟨hopt,hstart⟩,hend⟩
    exact ⟨Option.some.inj hopt,hlt,hstart,hend⟩
  · simp only [hlt,↓reduceIte] at hs
    rcases hs with ⟨⟨hopt,_⟩,_⟩
    cases hopt

theorem next_none_bound (iter iter' : Range)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (none,iter')) :
    iter.end.val ≤ iter.start.val := by
  have hs := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter
  rw [h,WP.spec_ok] at hs
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt,↓reduceIte] at hs
    rcases hs with ⟨⟨hopt,_⟩,_⟩
    cases hopt
  · omega

#print axioms next_some_step
#print axioms next_none_bound
end AspisR1CurrentPreparedClaim.ClaimTrace

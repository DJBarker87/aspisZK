import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1BatchedWeightsFinishExtraction
namespace batched_weights

private abbrev FinishIter :=
  core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)
private abbrev FinishBack := FinishIter → FinishIter
private abbrev FinishNextBack := FinishIter →
  Option (Std.Usize × aspis_core.field.QM31) → FinishIter

theorem finish_loop_body_some
    (self : BatchedWeights) (iter : FinishIter) (back : FinishBack)
    (i : Std.Usize) (x w : aspis_core.field.QM31)
    (iter1 : FinishIter) (nextBack : FinishNextBack)
    (hnext : core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
      .ok (some (i, x), iter1, nextBack))
    (hvalue : BatchedWeights.value self i = .ok w) :
    BatchedWeights.finish_loop.body self iter back =
      .ok (ControlFlow.cont
        (iter1, fun e => back (nextBack e (some (i, w))))) := by
  simp [BatchedWeights.finish_loop.body, hnext, hvalue]

theorem finish_loop_body_none
    (self : BatchedWeights) (iter : FinishIter) (back : FinishBack)
    (iter1 : FinishIter) (nextBack : FinishNextBack)
    (hnext : core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
      .ok (none, iter1, nextBack)) :
    BatchedWeights.finish_loop.body self iter back =
      .ok (ControlFlow.done (back (nextBack iter1 none))) := by
  simp [BatchedWeights.finish_loop.body, hnext]

#print axioms finish_loop_body_some
#print axioms finish_loop_body_none

end batched_weights
end AspisR1BatchedWeightsFinishExtraction

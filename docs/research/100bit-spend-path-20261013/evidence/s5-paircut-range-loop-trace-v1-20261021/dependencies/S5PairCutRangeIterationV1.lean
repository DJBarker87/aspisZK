import S5PairCutLoopFoldV1
import S4TailRangeNextRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5PairCutRangeIterationV1
open AspisR1S5PairCutLoopFoldV1
open AspisR1FastDotsTailRangeNextRootV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1WeightsPairCutEbyKDotOpsV1
local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

/-- A successful callback-push body step at the actual IteratorRange
successor, with the source's iterator transition fixed to `i ↦ i+1`. -/
theorem callback_body_at_range_successor
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (i n j : Usize) (pair pair1 : AspisR1WeightsPairCut.fast_pairing.EbyKDot)
    (value : PairWide) (scalar : PairQM)
    (hi : i.val < n.val) (hj : j.val = i.val + 1)
    (hread : read bytes i = .ok value)
    (hscalar : Slice.index_usize scratch i = .ok scalar)
    (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
      pair value scalar = .ok (.Ok (), pair1)) :
    pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch { start := i, «end» := n } pair =
      .ok (core.ops.control_flow.ControlFlow.Continue
        ({ start := j, «end» := n }, pair1)) := by
  have hnext := range_next_succ i n j hi hj
  exact emitted_body_success_continue
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
    read bytes scratch { start := i, «end» := n } { start := j, «end» := n }
    i pair pair1 value scalar hnext hread hscalar hpush

/-- At the actual range endpoint, the same source-shaped body takes its
`none` branch and returns the completed pair unchanged. -/
theorem callback_body_at_range_end
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (n : Usize)
    (pair : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    ∃ (iter : core.ops.range.Range Usize), pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch { start := n, «end» := n } pair =
      .ok (core.ops.control_flow.ControlFlow.Break
        (.Ok (), pair)) := by
  obtain ⟨iter, hnext⟩ := range_next_done n
  refine ⟨iter, ?_⟩
  simp [pushByteProductsBodyWith, hnext]

#print axioms callback_body_at_range_successor
#print axioms callback_body_at_range_end
end AspisR1S5PairCutRangeIterationV1

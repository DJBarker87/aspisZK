import AspisR1BatchedWeightsExtraction.Funs
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsNewLoopBodyActiveV1
abbrev Iter := core.ops.range.Range Std.Usize
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)
theorem cont_implies_active (weights : Slice aspis_core.field.QM31)
    (iter : Iter) (raw : Raw) (iterOut : Iter) (rawOut : Raw)
    (h : batched_weights.BatchedWeights.new_loop.body weights iter raw =
      .ok (.cont (iterOut, rawOut))) : iter.start.val < iter.end.val := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (done raw)
    | some index => do
        let w ← Slice.index_usize weights index
        let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
        let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
        let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
        let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
        let (_, back) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
        ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) = .ok (.cont (iterOut, rawOut)) at h
  by_contra hge
  have hnext := AspisR1.OccupancyRangeTraversal.next_done iter (Nat.le_of_not_gt hge)
  rw [hnext] at h
  simp only [bind_tc_ok] at h
  cases h
#print axioms cont_implies_active
end BatchedWeightsNewLoopBodyActiveV1

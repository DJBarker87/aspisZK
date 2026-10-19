import AspisR1BatchedWeightsExtraction.Funs
import BWResultBindInversionProbeV2
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
open BWResultBindInversionProbeV2
namespace BatchedWeightsNewLoopBodyIterV6
abbrev Iter := core.ops.range.Range Std.Usize
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)

theorem cont_success_iter (weights : Slice aspis_core.field.QM31)
    (iter : Iter) (raw : Raw) (iterOut : Iter) (rawOut : Raw)
    (h : batched_weights.BatchedWeights.new_loop.body weights iter raw =
      .ok (.cont (iterOut, rawOut))) :
    iterOut.start.val = iter.start.val + 1 ∧ iterOut.end.val = iter.end.val := by
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
  have hlt : iter.start.val < iter.end.val := by
    by_contra hn
    have hstop := AspisR1.OccupancyRangeTraversal.next_done iter (Nat.le_of_not_gt hn)
    simp only [hstop, bind_tc_ok] at h
    cases h
  obtain ⟨iter1, hnext, hstart, hend, _⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hlt
  let next := core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  let after := fun p : Option Std.Usize × Iter =>
    match p.1 with
    | none => ok (done raw)
    | some index => do
        let w ← Slice.index_usize weights index
        let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
        let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
        let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
        let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
        let (_, back) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
        ok (cont (p.2, back (Array.make 4#usize [i1, i3, i5, i7])) )
  obtain ⟨p, hp, hafter⟩ := bind_ok_inv next after (.cont (iterOut, rawOut)) h
  have hp' : p = (some iter.start, iter1) := by
    rw [show next = core.iter.range.IteratorRange.next core.iter.range.StepUsize iter by rfl,
      hnext] at hp
    injection hp with hpEq
    exact hpEq.symm
  subst p
  simp only [after] at hafter
  have hbody : (do
      let w ← Slice.index_usize weights iter.start
      let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
      let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
      let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
      let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
      ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) = .ok (.cont (iterOut, rawOut)) := hafter
  obtain ⟨w, hw, hbody⟩ := bind_ok_inv (Slice.index_usize weights iter.start)
    (fun w => do
      let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
      let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
      let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
      let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
      ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) (.cont (iterOut, rawOut)) hbody
  obtain ⟨i1, hi1, hbody⟩ := bind_ok_inv (lift (UScalar.cast UScalarTy.U64 w.c0.a))
    (fun i1 => do
      let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
      let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
      let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
      ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) (.cont (iterOut, rawOut)) hbody
  obtain ⟨i3, hi3, hbody⟩ := bind_ok_inv (lift (UScalar.cast UScalarTy.U64 w.c0.b))
    (fun i3 => do
      let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
      let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
      ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) (.cont (iterOut, rawOut)) hbody
  obtain ⟨i5, hi5, hbody⟩ := bind_ok_inv (lift (UScalar.cast UScalarTy.U64 w.c1.a))
    (fun i5 => do
      let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
      ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) (.cont (iterOut, rawOut)) hbody
  obtain ⟨i7, hi7, hbody⟩ := bind_ok_inv (lift (UScalar.cast UScalarTy.U64 w.c1.b))
    (fun i7 => do
      let (_, back) ← alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
      ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) (.cont (iterOut, rawOut)) hbody
  obtain ⟨z, hz, hfinal⟩ := bind_ok_inv
    (alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start)
    (fun z => match z with
      | (old, back) => ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7]))))
    (.cont (iterOut, rawOut)) hbody
  have hpair : (iter1, z.2 (Array.make 4#usize [i1, i3, i5, i7])) = (iterOut, rawOut) := by
    injection hfinal with hcf
    injection hcf
  have hiter : iter1 = iterOut := congrArg Prod.fst hpair
  subst iterOut
  exact ⟨by rw [hstart], by rw [hend]⟩
#print axioms cont_success_iter
end BatchedWeightsNewLoopBodyIterV6

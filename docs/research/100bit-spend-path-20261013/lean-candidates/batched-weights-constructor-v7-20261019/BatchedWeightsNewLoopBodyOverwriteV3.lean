import AspisR1BatchedWeightsExtraction.Funs
import BWResultBindInversionProbeV2
import BatchedWeightsNewLoopBodyActiveV1
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
open BWResultBindInversionProbeV2
open BatchedWeightsNewLoopBodyActiveV1
namespace BatchedWeightsNewLoopBodyOverwriteV3
abbrev Iter := core.ops.range.Range Std.Usize
abbrev Row := Array Std.U64 4#usize
abbrev Raw := alloc.vec.Vec Row

theorem cont_success_overwrite (weights : Slice aspis_core.field.QM31)
    (iter : Iter) (raw : Raw) (iterOut : Iter) (rawOut : Raw)
    (h : batched_weights.BatchedWeights.new_loop.body weights iter raw =
      .ok (.cont (iterOut, rawOut))) :
    ∃ w : aspis_core.field.QM31,
      Slice.index_usize weights iter.start = .ok w ∧
      rawOut = alloc.vec.Vec.set raw iter.start
        (Array.make 4#usize [
          UScalar.cast UScalarTy.U64 w.c0.a,
          UScalar.cast UScalarTy.U64 w.c0.b,
          UScalar.cast UScalarTy.U64 w.c1.a,
          UScalar.cast UScalarTy.U64 w.c1.b]) := by
  have hactive := cont_implies_active weights iter raw iterOut rawOut h
  obtain ⟨iter1, hnext, _, _, _⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hactive
  change (do
      let (o, iterSucc) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
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
          ok (cont (iterSucc, back (Array.make 4#usize [i1, i3, i5, i7])))
    ) = .ok (cont (iterOut, rawOut)) at h
  rcases bind_ok_inv
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter)
      (fun p => let (o, iterSucc) := p; match o with
        | none => ok (done raw)
        | some index => do
            let w ← Slice.index_usize weights index
            let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
            let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
            let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
            let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
            let (_, back) ← alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
            ok (cont (iterSucc, back (Array.make 4#usize [i1, i3, i5, i7]))))
      (cont (iterOut, rawOut)) h with ⟨next, hnextEq, hrest⟩
  have hnextEq' : next = (some iter.start, iter1) := by
    have hh := hnextEq
    rw [hnext] at hh
    injection hh with hp
    exact hp.symm
  subst next
  simp only at hrest
  rcases bind_ok_inv (Slice.index_usize weights iter.start)
      (fun w => do
        let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
        let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
        let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
        let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
        let p ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start
        let (_, back) := p
        ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7]))))
      (cont (iterOut, rawOut)) hrest with ⟨w, hw, htail⟩
  simp only [lift, bind_tc_ok] at htail
  rcases bind_ok_inv
      (alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw iter.start)
      (fun p => let (_, back) := p; ok (cont (iter1,
        back (Array.make 4#usize [UScalar.cast UScalarTy.U64 w.c0.a,
          UScalar.cast UScalarTy.U64 w.c0.b, UScalar.cast UScalarTy.U64 w.c1.a,
          UScalar.cast UScalarTy.U64 w.c1.b]))))
      (cont (iterOut, rawOut)) htail with ⟨pair, hmut, hfinal⟩
  rcases pair with ⟨old, back⟩
  have hout : back (Array.make 4#usize [
      UScalar.cast UScalarTy.U64 w.c0.a,
      UScalar.cast UScalarTy.U64 w.c0.b,
      UScalar.cast UScalarTy.U64 w.c1.a,
      UScalar.cast UScalarTy.U64 w.c1.b]) = rawOut := by
    injection hfinal with hcf
    injection hcf with hpair
    have hsecond := congrArg Prod.snd hpair
    exact hsecond
  have hback : back = alloc.vec.Vec.set raw iter.start := by
    simp only [alloc.vec.Vec.index_mut, core.slice.index.SliceIndexUsizeSlice,
      core.slice.index.Usize.index_mut, Slice.index_mut_usize] at hmut
    cases hr : Slice.index_usize (raw : Slice Row) iter.start with
    | fail e => simp [hr] at hmut
    | div => simp [hr] at hmut
    | ok oldRead =>
        simp only [hr, bind_tc_ok] at hmut
        have hpair : (oldRead, Slice.set raw iter.start) = (old, back) := by
          injection hmut
        change back = Slice.set raw iter.start
        exact (congrArg Prod.snd hpair).symm
  refine ⟨w, hw, ?_⟩
  rw [← hout, hback]
#print axioms cont_success_overwrite
end BatchedWeightsNewLoopBodyOverwriteV3

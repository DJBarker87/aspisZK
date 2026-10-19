import AspisR1BatchedWeightsExtraction.Funs
import BatchedWeightsIndexMutLengthV2
import BWResultBindInversionProbeV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
open BatchedWeightsIndexMutLengthV2
open BWResultBindInversionProbeV2
namespace BatchedWeightsNewLoopBodyLengthV18
abbrev Row := Array Std.U64 4#usize
abbrev Raw := alloc.vec.Vec Row
abbrev Iter := core.ops.range.Range Std.Usize

theorem cont_success_length (weights : Slice aspis_core.field.QM31)
    (iter : Iter) (raw : Raw) (iterOut : Iter) (out : Raw)
    (h : batched_weights.BatchedWeights.new_loop.body weights iter raw = .ok (cont (iterOut, out))) :
    out.length = raw.length := by
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
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
          ok (cont (iter1, index_mut_back (Array.make 4#usize [i1, i3, i5, i7])))
    ) = .ok (cont (iterOut, out)) at h
  rcases bind_ok_inv (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter)
      (fun p => let (o, iter1) := p; match o with
        | none => ok (done raw)
        | some index => do
          let w ← Slice.index_usize weights index
          let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
          let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
          let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
          let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
          ok (cont (iter1, index_mut_back (Array.make 4#usize [i1, i3, i5, i7]))))
      (cont (iterOut, out)) h
    with ⟨next, hnext, hrest⟩
  cases next with
  | mk o iter1 =>
    cases o with
    | none => simp at hrest
    | some index =>
      rcases bind_ok_inv (Slice.index_usize weights index)
          (fun w => do
            let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
            let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
            let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
            let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
            let p ← alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
            let (_, back) := p
            ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7]))))
          (cont (iterOut, out)) hrest
        with ⟨w, hw, htail⟩
      simp only [lift, bind_tc_ok] at htail
      rcases bind_ok_inv
          (alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index)
          (fun p => let (_, back) := p; ok (cont (iter1,
            back (Array.make 4#usize [UScalar.cast UScalarTy.U64 w.c0.a,
              UScalar.cast UScalarTy.U64 w.c0.b, UScalar.cast UScalarTy.U64 w.c1.a,
              UScalar.cast UScalarTy.U64 w.c1.b]))))
          (cont (iterOut, out)) htail
        with ⟨pair, hmut, hfinal⟩
      rcases pair with ⟨row, back⟩
      have hout : back (Array.make 4#usize [UScalar.cast UScalarTy.U64 w.c0.a,
              UScalar.cast UScalarTy.U64 w.c0.b, UScalar.cast UScalarTy.U64 w.c1.a,
              UScalar.cast UScalarTy.U64 w.c1.b]) = out := by
        injection hfinal with heq
        cases heq
        rfl
      rw [← hout]
      exact index_mut_callback_length raw index row back hmut _

theorem done_success_raw (weights : Slice aspis_core.field.QM31)
    (iter : Iter) (raw out : Raw)
    (h : batched_weights.BatchedWeights.new_loop.body weights iter raw = .ok (done out)) :
    out = raw := by
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
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
          ok (cont (iter1, index_mut_back (Array.make 4#usize [i1, i3, i5, i7])))
    ) = .ok (done out) at h
  rcases bind_ok_inv (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter)
      (fun p => let (o, iter1) := p; match o with
        | none => ok (done raw)
        | some index => do
          let w ← Slice.index_usize weights index
          let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
          let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
          let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
          let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
          ok (cont (iter1, index_mut_back (Array.make 4#usize [i1, i3, i5, i7]))))
      (done out) h
    with ⟨next, hnext, hrest⟩
  cases next with
  | mk o iter1 =>
    cases o with
    | none =>
      injection hrest with heq
      cases heq
      rfl
    | some index =>
      rcases bind_ok_inv (Slice.index_usize weights index)
          (fun w => do
            let i1 ← lift (UScalar.cast UScalarTy.U64 w.c0.a)
            let i3 ← lift (UScalar.cast UScalarTy.U64 w.c0.b)
            let i5 ← lift (UScalar.cast UScalarTy.U64 w.c1.a)
            let i7 ← lift (UScalar.cast UScalarTy.U64 w.c1.b)
            let p ← alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index
            let (_, back) := p
            ok (cont (iter1, back (Array.make 4#usize [i1, i3, i5, i7]))))
          (done out) hrest
        with ⟨w, hw, htail⟩
      simp only [lift, bind_tc_ok] at htail
      rcases bind_ok_inv
          (alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index)
          (fun p => let (_, back) := p; ok (cont (iter1,
            back (Array.make 4#usize [UScalar.cast UScalarTy.U64 w.c0.a,
              UScalar.cast UScalarTy.U64 w.c0.b, UScalar.cast UScalarTy.U64 w.c1.a,
              UScalar.cast UScalarTy.U64 w.c1.b]))))
          (done out) htail
        with ⟨pair, hmut, hfinal⟩
      injection hfinal with hbad
      cases hbad

#print axioms cont_success_length
#print axioms done_success_raw
end BatchedWeightsNewLoopBodyLengthV18

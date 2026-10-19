import BatchedWeightsNewLoopSuccessLengthV6
import BatchedWeightsNewLoopBodyOverwriteV3
import BWSetReadLemmasV4
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsNewLoopContentsV3
abbrev Iter := core.ops.range.Range Std.Usize
abbrev Row := Array Std.U64 4#usize
abbrev Raw := alloc.vec.Vec Row
def rowOf (w : aspis_core.field.QM31) : Row := Array.make 4#usize [
  UScalar.cast UScalarTy.U64 w.c0.a,
  UScalar.cast UScalarTy.U64 w.c0.b,
  UScalar.cast UScalarTy.U64 w.c1.a,
  UScalar.cast UScalarTy.U64 w.c1.b]
def body (weights : Slice aspis_core.field.QM31) : (Iter × Raw) → Result (ControlFlow (Iter × Raw) Raw) :=
  fun s => batched_weights.BatchedWeights.new_loop.body weights s.1 s.2

theorem usize_eq_of_val_eq (a b : Usize) (h : a.val = b.val) : a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UScalar.val] at h
      have hab := BitVec.eq_of_toNat_eq h
      subst bv
      rfl

theorem body_done_impossible (weights : Slice aspis_core.field.QM31) (iter : Iter) (raw : Raw) (out : Raw)
    (hlt : iter.start.val < iter.end.val)
    (h : body weights (iter, raw) = .ok (.done out)) : False := by
  obtain ⟨iter1, hnext, _, _, _⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hlt
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
    ) = .ok (.done out) at h
  rw [hnext] at h
  simp only [bind_tc_ok] at h
  cases hw : Slice.index_usize weights iter.start with
  | fail e => simp [hw, bind_tc_ok] at h
  | div => simp [hw, bind_tc_ok] at h
  | ok w =>
      simp only [hw, bind_tc_ok] at h
      cases h1 : lift (UScalar.cast UScalarTy.U64 w.c0.a) <;> simp [h1, bind_tc_ok] at h
      cases h3 : lift (UScalar.cast UScalarTy.U64 w.c0.b) <;> simp [h3, bind_tc_ok] at h
      cases h5 : lift (UScalar.cast UScalarTy.U64 w.c1.a) <;> simp [h5, bind_tc_ok] at h
      cases h7 : lift (UScalar.cast UScalarTy.U64 w.c1.b) <;> simp [h7, bind_tc_ok] at h
      cases hm : alloc.vec.Vec.index_mut_usize raw iter.start with
      | fail e => simp [hm] at h
      | div => simp [hm] at h
      | ok pair =>
          simp only [hm] at h
          cases h

theorem loop_success_contents_fuel (weights : Slice aspis_core.field.QM31)
    (iter : Iter) (raw : Raw) (start0 : Usize) (fuel : Nat)
    (hspan : iter.start.val + fuel = iter.end.val)
    (hstart : start0.val ≤ iter.start.val)
    (hlen : raw.length = iter.end.val)
    (hprefix : ∀ j : Usize, start0.val ≤ j.val → j.val < iter.start.val →
      Slice.index_usize (raw : Slice Row) j = (do let w ← Slice.index_usize weights j; ok (rowOf w)))
    (out : Raw)
    (h : batched_weights.BatchedWeights.new_loop iter weights raw = .ok out) :
    out.length = raw.length ∧
    ∀ j : Usize, start0.val ≤ j.val → j.val < iter.end.val →
      Slice.index_usize (out : Slice Row) j =
        (do let w ← Slice.index_usize weights j; ok (rowOf w)) := by
  change Aeneas.Std.loop (body weights) (iter, raw) = .ok out at h
  induction fuel generalizing iter raw start0 out with
  | zero =>
      have heq : iter.start.val = iter.end.val := by omega
      rcases BatchedWeightsNewLoopSuccessLengthV6.loop_success_cases (body weights) (iter, raw) out h with
        hdone | ⟨s, hcont, _⟩
      · have hout := BatchedWeightsNewLoopBodyLengthV18.done_success_raw weights iter raw out hdone
        subst out
        constructor
        · rfl
        · intro j hjlo hjhi
          rw [← heq] at hjhi
          exact hprefix j hjlo hjhi
      · have hactive := BatchedWeightsNewLoopBodyActiveV1.cont_implies_active weights iter raw s.1 s.2 (by simpa [body] using hcont)
        omega
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      rcases BatchedWeightsNewLoopSuccessLengthV6.loop_success_cases (body weights) (iter, raw) out h with
        hdone | ⟨s, hcont, htail⟩
      · exact False.elim (body_done_impossible weights iter raw out hlt (by simpa [body] using hdone))
      · rcases s with ⟨iterNext, rawNext⟩
        have hprogress := BatchedWeightsNewLoopBodyIterV6.cont_success_iter weights iter raw iterNext rawNext hcont
        rcases hprogress with ⟨hnextStart, hnextEnd⟩
        have hspanNext : iterNext.start.val + fuel = iterNext.end.val := by rw [hnextStart, hnextEnd]; omega
        have hlenNext : rawNext.length = iterNext.end.val := by rw [BatchedWeightsNewLoopBodyLengthV18.cont_success_length weights iter raw iterNext rawNext hcont, hlen, hnextEnd]
        obtain ⟨w, hw, hset⟩ := BatchedWeightsNewLoopBodyOverwriteV3.cont_success_overwrite weights iter raw iterNext rawNext hcont
        have hprefixNext : ∀ j : Usize, start0.val ≤ j.val → j.val < iterNext.start.val →
             Slice.index_usize (rawNext : Slice Row) j = (do let w ← Slice.index_usize weights j; ok (rowOf w)) := by
          intro j hjlo hjhi
          rw [hset]
          by_cases heq : j.val = iter.start.val
          · have hj : j = iter.start := usize_eq_of_val_eq j iter.start heq
            subst j
            change Slice.index_usize (alloc.vec.Vec.set raw iter.start (rowOf w) : Slice Row) iter.start =
              (do let w ← Slice.index_usize weights iter.start; ok (rowOf w))
            have hr := BWSetReadLemmasV4.set_read_eq raw iter.start (rowOf w) (by rw [hlen]; omega)
            simpa only [hw, bind_tc_ok] using hr
          · have hjold : j.val < iter.start.val := by rw [hnextStart] at hjhi; omega
            have hold := hprefix j hjlo hjold
            change Slice.index_usize (alloc.vec.Vec.set raw iter.start (rowOf w) : Slice Row) j =
              (do let w ← Slice.index_usize weights j; ok (rowOf w))
            have hread := BWSetReadLemmasV4.set_read_ne raw iter.start j (rowOf w) (Ne.symm heq)
            simpa only [hw, bind_tc_ok] using hread.trans hold
        have htail' : Aeneas.Std.loop (body weights) (iterNext, rawNext) = .ok out := htail
        have hresult := ih iterNext rawNext start0 hspanNext (by omega) hlenNext hprefixNext out htail'
        have houtlen : out.length = raw.length := by
          calc
            out.length = rawNext.length := hresult.1
            _ = iterNext.end.val := hlenNext
            _ = iter.end.val := by rw [hnextEnd]
            _ = raw.length := hlen.symm
        exact ⟨houtlen, by simpa [hnextEnd] using hresult.2⟩

#print axioms loop_success_contents_fuel
end BatchedWeightsNewLoopContentsV3

import HeapFilledOverwriteBodyV4
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1HeapFilled
open HeapFilledOverwriteBodyV4

namespace HeapFilledOverwriteLoopV1

abbrev Iter := core.ops.range.Range Std.Usize
abbrev Raw (T : Type) := alloc.vec.Vec T

def body {T : Type} (value : T) : (Iter × Raw T) →
    Result (ControlFlow (Iter × Raw T) (Raw T)) :=
  fun s => aspis_core.r0.heap.filled_loop.body value s.1 s.2

theorem body_cont_active {T : Type} (value : T) (iter : Iter) (raw : Raw T)
    (iterNext : Iter) (rawNext : Raw T)
    (h : body value (iter, raw) = .ok (.cont (iterNext, rawNext))) :
    iter.start.val < iter.end.val := by
  by_contra hn
  have hstop := AspisR1.OccupancyRangeTraversal.next_done iter (Nat.le_of_not_gt hn)
  change aspis_core.r0.heap.filled_loop.body value iter raw = .ok (.cont (iterNext, rawNext)) at h
  change (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (done raw)
      | some index => do
          let (_, back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice T) raw index
          let out1 := back value
          ok (cont (iter1, out1))) = .ok (.cont (iterNext, rawNext)) at h
  rw [hstop] at h
  simp only [bind_tc_ok] at h
  cases h

theorem body_done_impossible {T : Type} (value : T) (iter : Iter)
    (raw out : Raw T) (hlt : iter.start.val < iter.end.val)
    (h : body value (iter, raw) = .ok (.done out)) : False := by
  obtain ⟨iter1, hnext, _, _, _⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hlt
  change aspis_core.r0.heap.filled_loop.body value iter raw = .ok (.done out) at h
  change (do
      let (o, iter2) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (done raw)
      | some index => do
          let (_, back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice T) raw index
          let out1 := back value
          ok (cont (iter2, out1))) = .ok (.done out) at h
  rw [hnext] at h
  simp only [bind_tc_ok] at h
  cases hm : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice T) raw iter.start with
  | fail e => simp [hm, bind_tc_ok] at h
  | div => simp [hm, bind_tc_ok] at h
  | ok pair => simp [hm, bind_tc_ok] at h

theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hstep : step state with
  | fail e => simp [hstep] at h
  | div => simp [hstep] at h
  | ok cf =>
      cases cf with
      | done result =>
          simp [hstep] at h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp [hstep] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

theorem body_done_raw {T : Type} (value : T) (iter : Iter)
    (raw out : Raw T)
    (h : aspis_core.r0.heap.filled_loop.body value iter raw = .ok (.done out)) :
    out = raw := by
  change (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (done raw)
      | some index => do
          let (_, back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice T) raw index
          let out1 := back value
          ok (cont (iter1, out1))) = .ok (.done out) at h
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp [hn] at h
  | div => simp [hn] at h
  | ok pair =>
      rcases pair with ⟨o, iter1⟩
      simp only [hn, bind_tc_ok] at h
      cases o with
      | none =>
          injection h with hcf
          injection hcf with hout
          exact hout.symm
      | some index =>
          simp only [bind_tc_ok] at h
          cases hm : alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice T) raw index with
          | fail e => simp [hm, bind_tc_fail] at h
          | div => simp [hm, bind_tc_div] at h
          | ok p => simp [hm, bind_tc_ok] at h

theorem set_read_ne {T : Type} (raw : Raw T) (idx i : Std.Usize) (value : T)
    (hne : idx.val ≠ i.val) :
    Slice.index_usize (alloc.vec.Vec.set raw idx value : Slice T) i =
      Slice.index_usize (raw : Slice T) i := by
  simp [Slice.index_usize, alloc.vec.Vec.set, hne]

theorem set_read_eq {T : Type} (raw : Raw T) (idx : Std.Usize) (value : T)
    (hbound : idx.val < raw.length) :
    Slice.index_usize (alloc.vec.Vec.set raw idx value : Slice T) idx = .ok value := by
  simp [Slice.index_usize, alloc.vec.Vec.set, hbound]

theorem set_length {T : Type} (raw : Raw T) (idx : Std.Usize) (value : T) :
    (alloc.vec.Vec.set raw idx value).length = raw.length := by
  simp [alloc.vec.Vec.length, alloc.vec.Vec.set, Slice.set, List.length_set]

/-- Actual Aeneas body for the isolated post-resize overwrite loop: success
preserves vector length and makes every visited row read back as `value`.
The caller supplies only the untouched-prefix fact; the initial contents of
the resized vector are unconstrained. -/
theorem loop_success_fill_fuel {T : Type} (value : T)
    (iter : Iter) (raw : Raw T) (fuel : Nat)
    (hspan : iter.start.val + fuel = iter.end.val)
    (hlen : raw.length = iter.end.val)
    (hprefix : ∀ i : Std.Usize, i.val < iter.start.val →
      Slice.index_usize (raw : Slice T) i = .ok value)
    (out : Raw T)
    (h : aspis_core.r0.heap.filled_loop iter value raw = .ok out) :
    out.length = raw.length ∧
      ∀ i : Std.Usize, i.val < iter.end.val →
        Slice.index_usize (out : Slice T) i = .ok value := by
  change Aeneas.Std.loop (body value) (iter, raw) = .ok out at h
  induction fuel generalizing iter raw out with
  | zero =>
      have heq : iter.start.val = iter.end.val := by omega
      rcases loop_success_cases (body value) (iter, raw) out h with
        hdone | ⟨s, hcont, _⟩
      · have hout := body_done_raw value iter raw out hdone
        subst out
        constructor
        · rfl
        · intro i hi
          rw [← heq] at hi
          exact hprefix i hi
      · rcases s with ⟨iterNext, rawNext⟩
        have hactive := body_cont_active value iter raw iterNext rawNext hcont
        omega
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      rcases loop_success_cases (body value) (iter, raw) out h with
        hdone | ⟨s, hcont, htail⟩
      · exact False.elim (body_done_impossible value iter raw out hlt hdone)
      · rcases s with ⟨iterNext, rawNext⟩
        obtain ⟨hstart, hend, hset⟩ :=
          HeapFilledOverwriteBodyV4.body_cont_update value iter raw iterNext rawNext hcont
        have hspanNext : iterNext.start.val + fuel = iterNext.end.val := by
          rw [hstart, hend]
          omega
        have hlenNext : rawNext.length = iterNext.end.val := by
          rw [hset, set_length, hlen, hend]
        have hprefixNext : ∀ i : Std.Usize, i.val < iterNext.start.val →
            Slice.index_usize (rawNext : Slice T) i = .ok value := by
          intro i hi
          rw [hset]
          by_cases heq : i.val = iter.start.val
          · have hidx : i = iter.start := by
              apply UScalar.eq_of_val_eq
              exact heq
            subst i
            exact set_read_eq raw iter.start value (by rw [hlen]; omega)
          · have hold : i.val < iter.start.val := by rw [hstart] at hi; omega
            rw [set_read_ne raw iter.start i value (Ne.symm heq)]
            exact hprefix i hold
        have htail' : Aeneas.Std.loop (body value) (iterNext, rawNext) = .ok out := htail
        have hresult := ih iterNext rawNext hspanNext hlenNext hprefixNext out htail'
        constructor
        · calc
            out.length = rawNext.length := hresult.1
            _ = iterNext.end.val := hlenNext
            _ = iter.end.val := by rw [hend]
            _ = raw.length := hlen.symm
        · intro i hi
          have hiNext : i.val < iterNext.end.val := by rw [hend]; exact hi
          exact hresult.2 i hiNext

#print axioms loop_success_fill_fuel
end HeapFilledOverwriteLoopV1

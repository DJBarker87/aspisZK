-- PCWG_ generic lemmas for NCX_Reference.zero / required_binding_is_zero against the frozen array-equality emission.
import Aeneas
import PRVEq_P3W_LoopMap
import NCX_Reference.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace PRVEq_P3Y

theorem allM_ok {α : Type} (p : α → Bool) (l : List α) :
    List.allM (fun x => (ok (p x) : Result Bool)) l = ok (l.all p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.allM, ih]
    cases h : p a <;> simp [h, pure]

theorem zip_all_eq {α : Type} [DecidableEq α] (l1 l2 : List α) (h : l1.length = l2.length) :
    ((l1.zip l2).all (fun p => decide (p.1 = p.2))) = decide (l1 = l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a t ih =>
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp at h
      simp [List.zip_cons_cons, ih u h]

#print Aeneas.Std.Slice.index_usize
#print Aeneas.Std.Slice.len
theorem ne_u8 (x y : Std.U8) :
    (do let b ← core.cmp.PartialEqU8.ne x y; ok (decide ¬b = true) : Result Bool) = ok (decide (x = y)) := by
  simp [Aeneas.Std.core.cmp.PartialEqU8, Aeneas.Std.liftFun2, Aeneas.Std.core.cmp.impls.PartialEqU8.ne]
  exact ⟨UScalar.eq_of_val_eq, fun h => by rw [h]⟩

/-- array equality emission (core.array.equality.PartialEqArray.eq at u8) is the pure list equality -/
theorem arr_eq_u8 {N : Std.Usize} (a b : Std.Array Std.U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a.val = b.val)) := by
  unfold core.array.equality.PartialEqArray.eq
  have hl : a.length = b.length := by simp [Std.Array.length]
  rw [if_pos hl]
  have hf : (fun (x : Std.U8 × Std.U8) => (match x with
          | (x, y) => do
            let b ← core.cmp.PartialEqU8.ne x y
            ok (decide ¬b = true) : Result Bool)) = fun x => ok (decide (x.1 = x.2)) := by
    funext ⟨x, y⟩
    exact ne_u8 x y
  rw [hf, allM_ok]
  have hlen : a.val.length = b.val.length := by simpa [Std.Array.length] using hl
  rw [zip_all_eq a.val b.val hlen]

theorem zero_body_done (s : Slice Std.U8) (i : Std.Usize) (h : s.length ≤ i.val) :
    NCX_Reference.zero_loop.body s i = ok (done none) := by
  unfold NCX_Reference.zero_loop.body
  have hn : ¬ (i < Slice.len s) := by
    have := Slice.len_val s
    scalar_tac
  simp [hn]

theorem zero_body_bad (s : Std.Slice Std.U8) (i : Std.Usize) (h : i.val < s.length)
    (hz : s.val[i.val]'h ≠ 0#u8) :
    NCX_Reference.zero_loop.body s i = ok (done (some false)) := by
  unfold NCX_Reference.zero_loop.body
  have hl : i < Slice.len s := by
    have := Slice.len_val s
    scalar_tac
  have hx : Slice.index_usize s i = ok (s.val[i.val]'h) := by
    simp [Slice.index_usize, h]
  simp [hl, hx, hz]

theorem zero_body_cont (s : Std.Slice Std.U8) (i : Std.Usize) (h : i.val < s.length)
    (hz : s.val[i.val]'h = 0#u8) :
    ∃ j : Std.Usize, j.val = i.val + 1 ∧ NCX_Reference.zero_loop.body s i = ok (cont j) := by
  unfold NCX_Reference.zero_loop.body
  have hl : i < Slice.len s := by
    have := Slice.len_val s
    scalar_tac
  have hx : Slice.index_usize s i = ok (s.val[i.val]'h) := by
    simp [Slice.index_usize, h]
  have hmax : i.val + (1#usize).val ≤ Std.Usize.max := by
    have := s.property
    have : s.length ≤ Std.Usize.max := by simpa using s.property
    scalar_tac
  obtain ⟨z, hz', hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) hmax)
  refine ⟨z, by simpa using hv, ?_⟩
  simp [hl, hx, hz, hz']

end PRVEq_P3Y

import RPu_FIq_Native14
set_option autoImplicit false
namespace AspisR1.JFy_SliceSteps
open Aeneas Aeneas.Std Result
theorem list_drop_split {α : Type} (ys : List α) (i : Nat)
    (hi : i < ys.length) : ys.drop i = ys[i] :: ys.drop (i+1) := by
  induction ys generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < ys.length := by simpa using hi
          simpa using ih i hi'

theorem slice_next_step {T : Type} (iter : core.slice.iter.Iter T) (x : T)
    (xs : List T) (hdrop : iter.slice.val.drop iter.i = x :: xs) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (some x, {iter with i := iter.i + 1}) := by
  have hstep : iter.i < iter.slice.val.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hvalue : iter.slice.val[iter.i] = x := by
    have hsplit := list_drop_split iter.slice.val iter.i hstep
    rw [hdrop] at hsplit
    have hh := congrArg List.head? hsplit
    change some x = some (iter.slice.val[iter.i]) at hh
    exact (Option.some.inj hh).symm
  calc
    core.slice.iter.IteratorSliceIter.next iter =
        .ok (some iter.slice.val[iter.i], {iter with i := iter.i + 1}) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, hstep,
        ↓reduceDIte]
      rfl
    _ = .ok (some x, {iter with i := iter.i + 1}) := by rw [hvalue]

theorem slice_drop_step {T : Type} (iter : core.slice.iter.Iter T) (x : T)
    (xs : List T) (hdrop : iter.slice.val.drop iter.i = x :: xs) :
    iter.slice.val.drop (iter.i + 1) = xs := by
  have hstep : iter.i < iter.slice.val.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hsplit := list_drop_split iter.slice.val iter.i hstep
  rw [hdrop] at hsplit
  have ht := congrArg List.tail hsplit
  simpa using ht.symm


#print axioms list_drop_split
#print axioms slice_next_step
#print axioms slice_drop_step
end AspisR1.JFy_SliceSteps

import S3ActualLoop1BodyStepV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

private theorem list_drop_split {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) : xs.drop i = xs[i] :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simpa using ih i hi'

/-- One actual slice iterator read, expressed from the suffix it owns. -/
theorem slice_iter_next_some
    (iter : core.slice.iter.Iter field.WideExact)
    (x : field.WideExact) (tail : List field.WideExact)
    (hdrop : iter.slice.val.drop iter.i = x :: tail) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (some x, { iter with i := iter.i + 1 }) := by
  have hstep : iter.i < iter.slice.val.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons] at hlen
    omega
  have hvalue : iter.slice.val[iter.i] = x := by
    have hsplit := list_drop_split iter.slice.val iter.i hstep
    rw [hdrop] at hsplit
    have hh := congrArg List.head? hsplit
    change some x = some (iter.slice.val[iter.i]) at hh
    exact (Option.some.inj hh).symm
  calc
    core.slice.iter.IteratorSliceIter.next iter =
        .ok (some iter.slice.val[iter.i], { iter with i := iter.i + 1 }) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, hstep,
        ↓reduceDIte]
      rfl
    _ = .ok (some x, { iter with i := iter.i + 1 }) := by rw [hvalue]

/-- The actual `Enumerate<SliceIter>` call returns the current slice item and
advances both the underlying cursor and the enumerate count. -/
theorem enumerate_iter_next_some
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact))
    (x : field.WideExact) (tail : List field.WideExact)
    (hdrop : iter.iter.slice.val.drop iter.iter.i = x :: tail)
    (hcount : iter.count.val + 1 ≤ Usize.max) :
    ∃ next,
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter field.WideExact) iter =
          .ok (some (iter.count, x), next) ∧
      next.iter.slice = iter.iter.slice ∧
      next.iter.i = iter.iter.i + 1 ∧
      next.count.val = iter.count.val + 1 := by
  have hslice := slice_iter_next_some iter.iter x tail hdrop
  have hinner :
      (core.iter.traits.iterator.IteratorSliceIter field.WideExact).next iter.iter
        ⦃ (p : Option field.WideExact × core.slice.iter.Iter field.WideExact) =>
          p.1 = some x ∧ p.2 = { iter.iter with i := iter.iter.i + 1 } ⦄ := by
    change core.slice.iter.IteratorSliceIter.next iter.iter ⦃ (p :
      Option field.WideExact × core.slice.iter.Iter field.WideExact) =>
        p.1 = some x ∧ p.2 = { iter.iter with i := iter.iter.i + 1 } ⦄
    rw [hslice]
    simp [WP.spec_ok]
  have hspec := core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    (core.iter.traits.iterator.IteratorSliceIter field.WideExact)
    iter x { iter.iter with i := iter.iter.i + 1 } hinner hcount
  obtain ⟨result, hrun, hpost⟩ := WP.spec_imp_exists hspec
  rcases result with ⟨opt, next⟩
  rcases hpost with ⟨hopt, hiter, hcount'⟩
  subst opt
  refine ⟨next, hrun, ?_, ?_, hcount'⟩
  · rw [hiter]
  · rw [hiter]

#print axioms slice_iter_next_some
#print axioms enumerate_iter_next_some

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

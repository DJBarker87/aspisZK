import AspisR182IteratorDefault.FunsDefaultFold

/-! Generic Iterator::fold over the builtin slice iterator is expressed as a
monadic list fold carrying the FnMut environment. This leaves the distinct raw
FnMut closure shape in the full freeze extraction outside this theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R183DefaultFoldExecution

open Aeneas Aeneas.Std Result ControlFlow Error



def foldMutList {T B F : Type}
    (k : core.ops.function.FnMut F (B × T) B) :
    List T → F → B → Result (B × F)
  | [], f, acc => ok (acc, f)
  | x :: xs, f, acc => do
      let (acc1, f1) ← k.call_mut f (acc, x)
      foldMutList k xs f1 acc1

theorem drop_split {T : Type} (xs : List T) (i : Nat)
    (hi : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simpa using ih i hi'

theorem default_fold_slice {T B F : Type}
    (k : core.ops.function.FnMut F (B × T) B)
    (iter : core.slice.iter.Iter T) (init : B) (f : F) :
    AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorSliceIter T) k iter init f =
      (do
        let (acc, _) ← foldMutList k (iter.slice.val.drop iter.i) f init
        ok acc) := by
  unfold AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default
    AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default_loop
  let motive := fun (n : Nat) =>
    ∀ (iter : core.slice.iter.Iter T) (init : B) (f : F),
      iter.slice.len - iter.i = n →
      loop (fun (st : core.slice.iter.Iter T × F × B) =>
        AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default_loop.body
          (core.iter.traits.iterator.IteratorSliceIter T) k st.1 st.2.1 st.2.2)
          (iter, f, init) =
        (do
          let (acc, _) ← foldMutList k (iter.slice.val.drop iter.i) f init
          ok acc)
  have hloop : ∀ n, motive n := by
    intro n
    induction n with
    | zero =>
        intro iter init f hlen
        have hstop : ¬ iter.i < iter.slice.len := by omega
        have hstop' : ¬ iter.i < iter.slice.val.length := by simpa [Slice.len] using hstop
        have hnil : iter.slice.val.drop iter.i = [] := List.drop_eq_nil_of_le (by omega)
        rw [loop.eq_def]
        simp [AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default_loop.body,
          core.iter.traits.iterator.IteratorSliceIter,
          core.slice.iter.IteratorSliceIter.next, Slice.len, hstop', hnil,
          foldMutList]
    | succ n ih =>
        intro iter init f hlen
        have hlt : iter.i < iter.slice.len := by omega
        have hlen' : iter.slice.len - (iter.i + 1) = n := by omega
        have hdrop := drop_split iter.slice.val iter.i (by simpa [Slice.len] using hlt)
        rw [loop.eq_def]
        simp only [AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default_loop.body,
          core.iter.traits.iterator.IteratorSliceIter,
          core.slice.iter.IteratorSliceIter.next, dif_pos hlt,
          bind_tc_ok]
        rw [hdrop]
        cases hk : k.call_mut f (init, iter.slice.val[iter.i]) with
        | fail e =>
            simp only [foldMutList]
            erw [hk]
            simp [bind_tc_fail]
        | div =>
            simp only [foldMutList]
            erw [hk]
            simp [bind_tc_div]
        | ok pair =>
            rcases pair with ⟨acc1, f1⟩
            simp only [foldMutList]
            erw [hk]
            simp only [bind_tc_ok]
            have hrec := ih { iter with i := iter.i + 1 } acc1 f1 hlen'
            simpa [AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default_loop.body,
              core.iter.traits.iterator.IteratorSliceIter,
              core.slice.iter.IteratorSliceIter.next, Slice.len,
              foldMutList, hdrop] using hrec
  simpa [AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default,
    AspisR182IteratorDefault.core.iter.traits.iterator.Iterator.fold.default_loop] using
    hloop (iter.slice.len - iter.i) iter init f rfl

#print axioms foldMutList
#print axioms drop_split
#print axioms default_fold_slice

end AspisV8R19.R183DefaultFoldExecution

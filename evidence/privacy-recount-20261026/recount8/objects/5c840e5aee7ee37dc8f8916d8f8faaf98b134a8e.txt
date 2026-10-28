import R1Z.BuilderStdModels

/-! Order-preserving finite iterator collection. The trace premise specifies
only Iterator.next results, not a correctness conclusion for the bank. -/
set_option autoImplicit false
namespace R1Z.BuilderStdModels
open Aeneas Aeneas.Std Result
variable {I A B C : Type}

inductive FiniteTrace (it : core.iter.traits.iterator.Iterator I A) :
    I → List A → Prop
  | done (i i' : I) (h : it.next i = ok (none, i')) : FiniteTrace it i []
  | step (i i' : I) (x : A) (xs : List A)
      (h : it.next i = ok (some x, i')) (tail : FiniteTrace it i' xs) :
      FiniteTrace it i (x :: xs)

theorem collect_trace (it : core.iter.traits.iterator.Iterator I A)
    (i : I) (xs : List A) (ht : FiniteTrace it i xs) (acc : List A) :
    alloc.vec.FromIteratorVec.iterToList it i acc = ok (acc.reverse ++ xs) := by
  induction ht generalizing acc with
  | done i i' h =>
      rw [alloc.vec.FromIteratorVec.iterToList, h]
      simp
  | step i i' x xs h tail ih =>
      rw [alloc.vec.FromIteratorVec.iterToList, h]
      simp only [bind_tc_ok]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def mappedIterator (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I C) B where
  next := mapNext it f

theorem mapped_trace (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) (g : A → B)
    (hf : ∀ c x, f.call_mut c x = ok (g x, c))
    (i : I) (xs : List A) (ht : FiniteTrace it i xs) (c : C) :
    FiniteTrace (mappedIterator it f) ⟨i, c⟩ (xs.map g) := by
  induction ht with
  | done i i' h =>
      exact .done _ ⟨i', c⟩ (mapNext_none it f ⟨i, c⟩ i' h)
  | step i i' x xs h tail ih =>
      have hs : (mappedIterator it f).next ⟨i, c⟩ =
          ok (some (g x), ⟨i', c⟩) :=
        mapNext_some it f ⟨i, c⟩ i' x (g x) c h (hf c x)
      exact FiniteTrace.step _ _ _ _ hs ih

theorem collect_mapped_trace (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) (g : A → B)
    (hf : ∀ c x, f.call_mut c x = ok (g x, c))
    (i : I) (xs : List A) (ht : FiniteTrace it i xs) (c : C) :
    alloc.vec.FromIteratorVec.iterToList (mappedIterator it f) ⟨i, c⟩ [] =
      ok (xs.map g) := by
  exact collect_trace _ _ _ (mapped_trace it f g hf i xs ht c) []

#print axioms collect_trace
#print axioms mapped_trace
#print axioms collect_mapped_trace
end R1Z.BuilderStdModels

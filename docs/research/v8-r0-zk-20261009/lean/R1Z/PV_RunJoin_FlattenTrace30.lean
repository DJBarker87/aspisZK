import R1Z.PV_RunJoin_IteratorAny30
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FlattenTrace30
open Aeneas Aeneas.Std Result BuilderStdModels BuilderForestStd
variable {I A B U : Type}

def iterator (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (inner : core.iter.traits.iterator.Iterator U B) :
    core.iter.traits.iterator.Iterator (Flatten I A B U) B where
  next := flattenNext it conv inner

theorem same_next {S T : Type} (it : core.iter.traits.iterator.Iterator S T)
    (i j : S) (xs : List T) (hi : FiniteTrace it i xs) (hn : it.next j=it.next i) :
    FiniteTrace it j xs := by
  cases hi with
  | done i i' h => exact .done j i' (hn.trans h)
  | step i i' x xs h tail => exact .step j i' x xs (hn.trans h) tail
#print axioms same_next

theorem inner_trace (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (inner : core.iter.traits.iterator.Iterator U B)
    (i : I) (u : U) (xs ys : List B) (ht : FiniteTrace inner u xs)
    (tail : FiniteTrace (iterator it conv inner) ⟨i,none⟩ ys) :
    FiniteTrace (iterator it conv inner) ⟨i,some u⟩ (xs++ys) := by
  induction ht with
  | done u u' hn =>
    apply same_next _ _ _ _ tail
    exact flattenNext_skip it conv inner i u u' hn
  | step u u' x xs hn ht ih =>
    exact .step _ _ x _ (flattenNext_yield it conv inner i u u' x hn) ih
#print axioms inner_trace

theorem flatten_trace (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (inner : core.iter.traits.iterator.Iterator U B) (contents : A → List B)
    (hc : ∀ a, ∃ u, conv.into_iter a=ok u ∧ FiniteTrace inner u (contents a))
    (i : I) (xs : List A) (ht : FiniteTrace it i xs) :
    FiniteTrace (iterator it conv inner) ⟨i,none⟩ (xs.flatMap contents) := by
  induction ht with
  | done i i' hn => exact .done _ _ (flattenNext_done it conv inner i i' hn)
  | step i i' a xs hn tail ih =>
    obtain ⟨u,hu,ht⟩ := hc a
    have hs := inner_trace it conv inner i' u (contents a) (xs.flatMap contents) ht ih
    apply same_next _ _ _ _ hs
    exact flattenNext_open it conv inner i i' a u hn hu
#print axioms flatten_trace
end R1Z.PV_RunJoin_FlattenTrace30

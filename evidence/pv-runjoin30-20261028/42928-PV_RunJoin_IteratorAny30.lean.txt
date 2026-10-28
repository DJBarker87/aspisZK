import R1Z.BuilderForestStd
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IteratorAny30
open Aeneas Aeneas.Std Result BuilderStdModels BuilderForestStd
variable {I A C : Type}

theorem any_trace (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A Bool) (g : A → Bool)
    (hf : ∀ c x, f.call_mut c x = ok (g x,c))
    (i : I) (xs : List A) (ht : FiniteTrace it i xs) (c : C) :
    ∃ b after, iterAny it f i c = ok (b,after) ∧
      (b=false ↔ ∀ x ∈ xs, g x=false) := by
  induction ht generalizing c with
  | done i i' h =>
    exact ⟨false,i',any_done it f i i' c h,by simp⟩
  | step i i' x xs hn tail ih =>
    cases hg : g x with
    | true =>
      refine ⟨true,i',any_stop it f i i' c c x hn ?_,?_⟩
      · simpa only [hg] using hf c x
      · simp only [Bool.true_eq_false,false_iff,List.forall_mem_cons]
        intro h
        have hx := h.1
        rw [hg] at hx
        cases hx
    | false =>
      obtain ⟨b,after,hr,hb⟩ := ih c
      refine ⟨b,after,?_,?_⟩
      · rw [any_continue it f i i' c c x hn (by simpa only [hg] using hf c x)]
        exact hr
      · simpa only [List.forall_mem_cons,hg,true_and] using hb
#print axioms any_trace

#print Aeneas.Std.core.iter.traits.iterator.IteratorSliceIter
#print Aeneas.Std.SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
end R1Z.PV_RunJoin_IteratorAny30

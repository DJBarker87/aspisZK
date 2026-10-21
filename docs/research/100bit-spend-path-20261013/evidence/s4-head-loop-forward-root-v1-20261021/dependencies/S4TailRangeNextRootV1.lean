import S4ActualTailBodyForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailRangeNextRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Range TailBody)

theorem range_next_succ (i n j : Usize) (hi : i.val<n.val) (hj : j.val=i.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
      {start:=i,«end»:=n} = .ok (some i,{start:=j,«end»:=n}) := by
  have hs := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) ({start:=i,«end»:=n} : Range)
  obtain ⟨⟨opt,it⟩,hr,hpost⟩ := WP.spec_imp_exists hs
  simp only [hi,↓reduceIte] at hpost
  rcases hpost with ⟨⟨ho,hstart⟩,hend⟩
  have hs' : it.start=j := UScalar.eq_of_val_eq (hstart.trans hj.symm)
  have he : it = {start:=j,«end»:=n} := by
    cases it with
    | mk s e =>
      change s=j at hs'
      change e=n at hend
      cases hs'
      cases hend
      rfl
  simpa only [ho,he] using hr

theorem range_next_done (n : Usize) :
    ∃ it : Range, core.iter.range.IteratorRange.next core.iter.range.StepUsize
      {start:=n,«end»:=n} = .ok (none,it) := by
  have hs := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) ({start:=n,«end»:=n} : Range)
  obtain ⟨⟨opt,it⟩,hr,hpost⟩ := WP.spec_imp_exists hs
  simp only [Nat.lt_irrefl,↓reduceIte] at hpost
  exact ⟨it,by simpa only [hpost.1.1] using hr⟩

theorem actual_tail_body_done (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot n : Usize) (tail : Tail) :
    TailBody ops a g slot {start:=n,«end»:=n} tail = .ok (.done tail) := by
  obtain ⟨it,hnext⟩ := range_next_done n
  simp [TailBody,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,
    hnext]

#print axioms range_next_succ
#print axioms range_next_done
#print axioms actual_tail_body_done
end AspisR1FastDotsTailRangeNextRootV1

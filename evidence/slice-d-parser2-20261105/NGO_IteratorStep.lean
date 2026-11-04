import NGO_ChunkSchedule
import NGO_TraceTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_IteratorStep
abbrev Native := core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8)
abbrev Index := core.ops.range.Range Usize
/-- Both original chunks/enumerate and emitted index iterator return the SAME
index and advance by one. The head is a typed borrowed chunk, never fresh bytes. -/
theorem live (count finish : Usize) (chunk remainder : Slice U8) (tail : List (Slice U8))
    (inside : count.val<finish.val) :
    ∃ next : Usize,
      next.val=count.val+1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorChunksExact U8)
        ({iter:={chunks:=chunk::tail,remainder},count} : Native) =
          ok (some (count,chunk),{iter:={chunks:=tail,remainder},count:=next}) ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=count,«end»:=finish} : Index) =
          ok (some count,{start:=next,«end»:=finish}) := by
  obtain ⟨next,addition,value⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=count) (y:=1#usize) (by scalar_tac))
  obtain ⟨⟨o,iter⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      ({start:=count,«end»:=finish} : Index) inside)
  have same : iter={start:=next,«end»:=finish} := by
    cases iter
    simp only [core.ops.range.Range.mk.injEq]
    exact ⟨UScalar.eq_of_val_eq (by simpa using hs.trans value.symm),he⟩
  refine ⟨next,by simpa using value,?_,?_⟩
  · simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.iter.traits.iterator.IteratorChunksExact,core.slice.iter.IteratorChunksExact.next,
      addition]
  · simpa only [ho,same] using run

/-- Empty native suffix agrees with stopping at the emitted end. -/
theorem stop (count : Usize) (remainder : Slice U8) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorChunksExact U8)
      ({iter:={chunks:=[],remainder},count} : Native) =
        ok (none,{iter:={chunks:=[],remainder},count}) ∧
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
      ({start:=count,«end»:=count} : Index) =
        ok (none,{start:=count,«end»:=count}) := by
  constructor
  · rfl
  · obtain ⟨⟨o,iter⟩,run,ho,hi⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl)
        ({start:=count,«end»:=count} : Index) (by simp))
    simpa only [ho,hi] using run
#print axioms live
#print axioms stop
end NGO_IteratorStep

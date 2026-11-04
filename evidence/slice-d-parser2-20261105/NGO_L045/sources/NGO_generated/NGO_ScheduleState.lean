import NGO_ChunksNativeStart
import NGO_IteratorIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ScheduleState
abbrev CE := core.slice.iter.ChunksExact U8
abbrev Iter := NGO_IteratorStep.Native
def state (original : CE) (count : Usize) : Iter :=
  {iter:={chunks:=original.chunks.drop count.val,remainder:=original.remainder},count}
/-- The original iterator has exactly the suffix selected by the emitted index. -/
theorem step (original : CE) (count finish next : Usize)
    (length : original.chunks.length=finish.val) (inside : count.val<finish.val)
    (advance : next.val=count.val+1) :
    ∃ chunk,
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorChunksExact U8) (state original count) =
          ok (some (count,chunk),state original next) ∧
      original.chunks[count.val]'(by omega)=chunk := by
  have present : original.chunks.drop count.val≠[] := by
    intro empty
    have h:=congrArg List.length empty
    simp only [List.length_drop,List.length_nil] at h
    omega
  cases suffixEq : original.chunks.drop count.val with
  | nil => contradiction
  | cons chunk tail =>
    obtain ⟨next1,value,native,indexed⟩ := NGO_IteratorStep.live count finish chunk original.remainder tail inside
    have same : next1=next := UScalar.eq_of_val_eq (value.trans advance.symm)
    have tailEq : original.chunks.drop next.val=tail := by
      rw [advance,←List.drop_drop]
      simp [suffixEq]
    refine ⟨chunk,?_,?_⟩
    · simpa only [state,suffixEq,tailEq,same] using native
    · have head := congrArg (fun xs : List (Slice U8)=>xs[0]?) suffixEq
      simpa using head

theorem stop (original : CE) (count : Usize) (length : original.chunks.length=count.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorChunksExact U8) (state original count)=
        ok (none,state original count) := by
  have empty : original.chunks.drop count.val=[] := by rw [←length];simp
  simpa only [state,empty] using (NGO_IteratorStep.stop count original.remainder).1
#print axioms step
#print axioms stop
end NGO_ScheduleState

import PCB_AppendFullRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_Iterator

def cursor {T : Type} (s : Slice T) (i : Nat) (count : Usize) :
    core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T) :=
  ⟨⟨s,i⟩,count⟩

theorem done {T : Type} (s : Slice T) (i : Nat) (count : Usize)
    (stop : s.length ≤ i) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter T) (cursor s i count) =
      ok (none, cursor s i count) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
    core.iter.traits.iterator.IteratorSliceIter cursor
  simp only [core.slice.iter.IteratorSliceIter.next]
  simp only [dif_neg (show ¬ i < s.len.val by change ¬ i < s.length; omega),bind_tc_ok]

theorem step {T : Type} (s : Slice T) (i : Nat) (count : Usize)
    (live : i < s.length) (room : count.val + 1 ≤ Usize.max) :
    ∃ count' : Usize, count'.val = count.val + 1 ∧
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter T) (cursor s i count) =
      ok (some (count,s[i]), cursor s (i+1) count') := by
  obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=count) (y:=1#usize) (by scalar_tac))
  refine ⟨out,by scalar_tac,?_⟩
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
    core.iter.traits.iterator.IteratorSliceIter cursor
  simp only [core.slice.iter.IteratorSliceIter.next]
  simp only [dif_pos (show i < s.len.val from live),bind_tc_ok]
  rw [ho]
  rfl

#print axioms done
#print axioms step
end PCF_Iterator

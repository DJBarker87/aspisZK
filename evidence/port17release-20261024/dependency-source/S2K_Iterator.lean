import S2K_LoopStep

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.Iterator
open LoopStep

def cursor (rows : Array Digest 20#usize) (count : Usize) : Iter :=
  ⟨⟨rows.to_slice,count.val⟩,count⟩

theorem next_row (rows : Array Digest 20#usize) (count : Usize)
    (range : count.val < 20) :
    next (cursor rows count) = ok
      (some (count,rows.val[count.val]'(by have := rows.property; change rows.val.length = 20 at this; omega)),
       cursor rows (Usize.ofNatCore (count.val+1) (by scalar_tac))) := by
  have inc : count + 1#usize = ok (Usize.ofNatCore (count.val+1) (by scalar_tac)) := by
    change UScalar.tryMk .Usize (count.val+1) = _
    simp only [UScalar.tryMk, UScalar.tryMkOpt]
    rw [dif_pos ((UScalar.check_bounds_eq_inBounds .Usize (count.val+1)).mpr (by scalar_tac))]
    rfl
  have valid : count.val < rows.to_slice.len.val := by
    simp only [Array.to_slice, Slice.len_val, rows.property]
    exact range
  simp only [next, cursor, core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next,
    dif_pos valid, bind_tc_ok, inc]
  rfl

theorem exhausted (rows : Array Digest 20#usize) :
    next (cursor rows 20#usize) = ok (none,cursor rows 20#usize) := by
  have invalid : ¬ (20#usize).val < rows.to_slice.len.val := by
    simp only [Array.to_slice, Slice.len_val, rows.property]
    decide
  simp only [next, cursor, core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next,
    dif_neg invalid, bind_tc_ok]

#print axioms next_row
#print axioms exhausted
end AspisR1.S2K.Iterator

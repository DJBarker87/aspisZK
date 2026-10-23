import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6ForestArrayWrites

/-- The exact emitted mutable-range/copy/back sequence. -/
def copyRange {N : Usize} (a : Array U8 N) (first last : Usize)
    (source : Slice U8) : Result (Array U8 N) := do
  let (slice,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) a {start:=first,«end»:=last}
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice source
  ok (back copied)

/-- TOTAL one-range write on its actual bounds, including the full array frame.
No independent copy success or desired output equation is a premise. -/
theorem copyRange_total {N : Usize} (a : Array U8 N) (first last : Usize)
    (source : Slice U8) (horder : first.val≤last.val) (hbound : last.val≤N.val)
    (hwidth : source.val.length=last.val-first.val) :
    ∃ out,copyRange a first last source=ok out ∧
      out.val=a.val.setSlice! first.val source.val := by
  obtain ⟨⟨slice,back⟩,hindex,hvalue,hlength,hback⟩ := spec_imp_exists
    (Array.index_mut_SliceIndexRangeUsizeSlice.step a {start:=first,«end»:=last}
      (by scalar_tac) (by scalar_tac))
  have sameLength : slice.length=source.length := by
    change slice.val.length=source.val.length
    exact hlength.trans hwidth.symm
  obtain ⟨copied,hcopy,hcopied⟩ := spec_imp_exists
    (core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU8 slice source sameLength)
  subst copied
  refine ⟨back source,?_,hback source⟩
  unfold copyRange
  rw [hindex,bind_tc_ok]
  change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice source
             ok (back copied))=ok (back source)
  rw [hcopy,bind_tc_ok]

#print axioms copyRange_total
end AspisS6ForestArrayWrites

import JHf_Scan
set_option autoImplicit false
namespace NDM_ScanWindow
open Aeneas Aeneas.Std Result

def prefix (bytes : Slice U8) : Slice U8 :=
 ⟨bytes.val.take 688,by
  have h:=bytes.property
  simp only [List.length_take]
  omega⟩

theorem length (bytes : Slice U8) (bound : 688≤bytes.val.length) :
 (prefix bytes).val.length=688 := by
 simp [prefix,List.length_take,Nat.min_eq_left bound]

theorem byte (bytes : Slice U8) (i : Nat) (bound : i<688) :
 (prefix bytes).val[i]?=bytes.val[i]? := by
 simp only [prefix,List.getElem?_take_of_lt bound]

/-- Computed source prefix, not an assumed decoder input. -/
theorem call (bytes : Slice U8) (bound : 688≤bytes.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  bytes {start:=0#usize,«end»:=688#usize}=ok (prefix bytes) := by
 obtain ⟨out,run,contents,size⟩:=WP.spec_imp_exists
  (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
   (⟨0#usize,688#usize⟩ : core.ops.range.Range Usize) bytes (by decide) (by simpa using bound))
 have same : out=prefix bytes := by
  apply Subtype.ext
  rw [contents]
  simp [List.slice,prefix]
 exact run.trans (congrArg ok same)

#print axioms length
#print axioms byte
#print axioms call
end NDM_ScanWindow

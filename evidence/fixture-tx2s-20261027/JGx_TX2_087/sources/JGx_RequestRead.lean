import JGx_RequestBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RequestRead
open Aeneas Aeneas.Std Result

#print core.slice.index.SliceIndexRangeToUsizeSlice.get
theorem source (payload : Array U8 316#usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (JGx_RequestBytes.value payload) {«end»:=4#usize}=ok (some JGx_RequestBytes.magic) := by
  unfold core.slice.Slice.get
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice]
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.get
  rw [JGx_RequestBytes.length]
  rfl
#print axioms source
end AspisR1.JGx_RequestRead
end

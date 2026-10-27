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
  have hlen : (JGx_RequestBytes.value payload).length=320 := congrArg UScalar.val (JGx_RequestBytes.length payload)
  rw [if_pos (by change 4≤(JGx_RequestBytes.value payload).length;rw [hlen];decide)]
  apply congrArg ok
  apply congrArg some
  apply Subtype.ext
  exact JGx_RequestBytes.first payload

#print axioms source
end AspisR1.JGx_RequestRead
end

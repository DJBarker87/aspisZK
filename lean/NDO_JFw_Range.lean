import NDO_JFw_Frames
set_option autoImplicit false
namespace AspisR1.JFw_Range
open Aeneas Aeneas.Std Result

theorem read (start stop : Usize) (order : start ≤ stop) (bound : stop.val ≤ 57607) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=start,«end»:=stop} =
      ok (JFw_Frames.window start.val (stop.val-start.val)) := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  have length : JFx_NativeBytes.proof.length = 57607 := JFx_NativeBytes.proofBytes_length
  have fits : start ≤ stop ∧ stop.val ≤ JFx_NativeBytes.proof.length := ⟨order,by rw [length];exact bound⟩
  rw [if_pos fits]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

#print axioms read
end AspisR1.JFw_Range

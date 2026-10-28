import NDO_JHd_RequestSegments
set_option autoImplicit false
namespace AspisR1.JHd_RequestSuffix
open Aeneas Aeneas.Std Result WP JHd_RequestWindow
attribute [local irreducible] value JHb_DataRequest.bytes JFu_PublicRange.payment

theorem source : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
    value {start:=104#usize}=ok JFu_PublicRange.payment := by
  have size : value.to_slice.val.length=320 := by
    simp only [value,Array.to_slice]
    exact JHb_DataRequest.length
  have take : (JHb_DataRequest.bytes.drop 104).take 216=JHb_DataRequest.bytes.drop 104 :=
    List.take_of_length_le (by rw [List.length_drop,JHb_DataRequest.length])
  have spec : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      value {start:=104#usize} ⦃ out => out=window 104 216 (by decide) ⦄ := by
    unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    step*
    all_goals try (change 104≤value.to_slice.val.length;omega)
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,value,Array.to_slice,window,
      show 320-104=216 from rfl,take]
      using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same,JHd_RequestSegments.payment] at call
  exact call
#print axioms source
end AspisR1.JHd_RequestSuffix

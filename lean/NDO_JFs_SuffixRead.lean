import NDO_JFs_RangeFrom
set_option autoImplicit false
namespace AspisR1.JFs_SuffixRead
open Aeneas Aeneas.Std Result WP

theorem source (bytes : Slice U8) (start : Usize) (bound : start.val≤bytes.length)
    (out : Slice U8) (selected : bytes.val.drop start.val=out.val) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes {start:=start}=ok out := by
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes {start:=start} ⦃ result => result=out ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simp_all only [List.slice,selected]
  obtain ⟨result,call,same⟩:=WP.spec_imp_exists spec
  exact same ▸ call

#print axioms source
end AspisR1.JFs_SuffixRead

import NDO_JFt_Range
set_option autoImplicit false
namespace AspisR1.JFs_RangeFrom
open Aeneas Aeneas.Std Result WP

theorem read (off n : Nat) (bound : off+n≤1880) (start : Usize) (inside : start.val≤n) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (JFu_PublicRange.segment off n bound) {start:=start}=
      ok (JFu_PublicRange.segment (off+start.val) (n-start.val) (by omega)) := by
  have size:=JFu_PublicRange.length off n bound
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (JFu_PublicRange.segment off n bound) {start:=start}
      ⦃ out => out=JFu_PublicRange.segment (off+start.val) (n-start.val) (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,JFu_PublicRange.segment,List.drop_take,List.drop_drop] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms read
end AspisR1.JFs_RangeFrom

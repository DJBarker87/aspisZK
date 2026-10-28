import NDO_JFt_Range
set_option autoImplicit false
namespace AspisR1.JFt_LocalWindow
open Aeneas Aeneas.Std Result WP

theorem selected (off n start count : Nat) (bound : off+start+count≤1880)
    (inside : start+count≤n) (xs : List U8)
    (window : (JFx_NativeBytes.publicInput.val.drop off).take n=xs) :
    (JFu_PublicRange.segment (off+start) count bound).val=(xs.drop start).take count := by
  rw [←window]
  exact (JFu_PublicRange.nested _ off n start count inside).symm

theorem firstn (off n : Nat) (count : Usize) (bound : off+n≤1880) (inside : count.val≤n) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (JFu_PublicRange.segment off n bound) {«end»:=count}=
    ok (JFu_PublicRange.segment off count.val (by omega)) := by
  have size:=JFu_PublicRange.length off n bound
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (JFu_PublicRange.segment off n bound) {«end»:=count}
      ⦃ out => out=JFu_PublicRange.segment off count.val (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [JFu_PublicRange.segment,List.slice,List.drop_zero,List.take_take,Nat.sub_zero,
      Nat.min_eq_left inside] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms selected
#print axioms firstn
end AspisR1.JFt_LocalWindow

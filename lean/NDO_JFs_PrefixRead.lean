import NDO_JFt_LocalWindow
set_option autoImplicit false
namespace AspisR1.JFs_PrefixRead
open Aeneas Aeneas.Std Result WP

theorem source (bytes : Slice U8) (n : Usize) (bound : n.val≤bytes.length)
    (out : Slice U8) (selected : bytes.val.take n.val=out.val) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      bytes {«end»:=n}=ok out := by
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      bytes {«end»:=n} ⦃ result => result=out ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simp_all only [List.slice,List.drop_zero,Nat.sub_zero,selected]
  obtain ⟨result,call,same⟩:=WP.spec_imp_exists spec
  exact same ▸ call

#print axioms source
end AspisR1.JFs_PrefixRead

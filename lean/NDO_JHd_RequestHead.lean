import NDO_JHd_RequestWindow
import JHd_RequestFuns
set_option autoImplicit false
namespace AspisR1.JHd_RequestHead
open Aeneas Aeneas.Std Result WP JHd_RequestWindow

def magic : Slice U8 := ⟨[65#u8,83#u8,81#u8,56#u8],by simp;scalar_tac⟩

attribute [local irreducible] value magic

theorem first : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
    value {«end»:=4#usize}=ok magic := by
  have selected : JHb_DataRequest.bytes.take 4=magic.val := by unfold magic;rfl
  have size : value.to_slice.val.length=320 := by
    simp only [value,Array.to_slice]
    exact JHb_DataRequest.length
  have spec : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
      value {«end»:=4#usize} ⦃ out => out=magic ⦄ := by
    unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    step*
    all_goals try (change 4≤value.to_slice.val.length;omega)
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,value,Array.to_slice,List.drop_zero,selected] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call
#print axioms first

theorem b4 : Array.index_usize value 4#usize=ok 1#u8 := by unfold value;rfl
theorem b5 : Array.index_usize value 5#usize=ok 1#u8 := by unfold value;rfl
theorem b6 : Array.index_usize value 6#usize=ok 1#u8 := by unfold value;rfl
theorem b7 : Array.index_usize value 7#usize=ok 0#u8 := by unfold value;rfl
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
end AspisR1.JHd_RequestHead

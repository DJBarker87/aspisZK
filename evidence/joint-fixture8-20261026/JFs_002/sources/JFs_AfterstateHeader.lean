import JFt_LocalWindow
import JFt_Index
import JFu_PublicMeta06
set_option autoImplicit false
namespace AspisR1.JFs_AfterstateHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

def magic : Slice U8 := ⟨JFu_PublicMeta06.bytes.take 4,by simp [JFu_PublicMeta06.bytes];scalar_tac⟩
theorem magic_selected : JFu_PublicRange.segment 976 4 (by decide)=magic := by
  apply Subtype.ext
  exact JFt_LocalWindow.selected 976 16 0 4 (by decide) (by decide) _ JFu_PublicMeta06.selected

theorem magic_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC {start:=0#usize,«end»:=4#usize}=ok magic := by rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) magic magic=ok false := by rfl

theorem b4 : Slice.index_usize JFu_PublicRange.afterstate 4#usize=ok 1#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.afterstate,JFu_PublicRange.length];decide) 1#u8
  have h:=congrArg (fun xs : List U8 => xs[4]?) JFu_PublicMeta06.selected
  change ((JFx_NativeBytes.publicInput.val.drop 976).take 688)[4]?=some 1#u8
  rw [List.getElem?_take_of_lt (by decide : 4<688)]
  simpa only [List.getElem?_take_of_lt (by decide : 4<16),JFu_PublicMeta06.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b5 : Slice.index_usize JFu_PublicRange.afterstate 5#usize=ok 1#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.afterstate,JFu_PublicRange.length];decide) 1#u8
  have h:=congrArg (fun xs : List U8 => xs[5]?) JFu_PublicMeta06.selected
  change ((JFx_NativeBytes.publicInput.val.drop 976).take 688)[5]?=some 1#u8
  rw [List.getElem?_take_of_lt (by decide : 5<688)]
  simpa only [List.getElem?_take_of_lt (by decide : 5<16),JFu_PublicMeta06.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b6 : Slice.index_usize JFu_PublicRange.afterstate 6#usize=ok 1#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.afterstate,JFu_PublicRange.length];decide) 1#u8
  have h:=congrArg (fun xs : List U8 => xs[6]?) JFu_PublicMeta06.selected
  change ((JFx_NativeBytes.publicInput.val.drop 976).take 688)[6]?=some 1#u8
  rw [List.getElem?_take_of_lt (by decide : 6<688)]
  simpa only [List.getElem?_take_of_lt (by decide : 6<16),JFu_PublicMeta06.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b7 : Slice.index_usize JFu_PublicRange.afterstate 7#usize=ok 1#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.afterstate,JFu_PublicRange.length];decide) 1#u8
  have h:=congrArg (fun xs : List U8 => xs[7]?) JFu_PublicMeta06.selected
  change ((JFx_NativeBytes.publicInput.val.drop 976).take 688)[7]?=some 1#u8
  rw [List.getElem?_take_of_lt (by decide : 7<688)]
  simpa only [List.getElem?_take_of_lt (by decide : 7<16),JFu_PublicMeta06.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

#print axioms magic_selected
#print axioms magic_array
#print axioms magic_compare
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
end AspisR1.JFs_AfterstateHeader

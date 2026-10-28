import NDO_JFt_LocalWindow
import NDO_JFs_IndexWindow
import NDO_JFu_PublicMeta06
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
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC {start:=0#usize,«end»:=4#usize}=ok magic := by
  unfold POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC
  rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) magic magic=ok false := by rfl

theorem b4 : Slice.index_usize JFu_PublicRange.afterstate 4#usize=ok 1#u8 := by
  exact JFs_IndexWindow.source 976 688 16 (by decide) 4#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta06.bytes JFu_PublicMeta06.selected (by rfl)

theorem b5 : Slice.index_usize JFu_PublicRange.afterstate 5#usize=ok 1#u8 := by
  exact JFs_IndexWindow.source 976 688 16 (by decide) 5#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta06.bytes JFu_PublicMeta06.selected (by rfl)

theorem b6 : Slice.index_usize JFu_PublicRange.afterstate 6#usize=ok 1#u8 := by
  exact JFs_IndexWindow.source 976 688 16 (by decide) 6#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta06.bytes JFu_PublicMeta06.selected (by rfl)

theorem b7 : Slice.index_usize JFu_PublicRange.afterstate 7#usize=ok 1#u8 := by
  exact JFs_IndexWindow.source 976 688 16 (by decide) 7#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta06.bytes JFu_PublicMeta06.selected (by rfl)

#print axioms magic_selected
#print axioms magic_array
#print axioms magic_compare
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
end AspisR1.JFs_AfterstateHeader

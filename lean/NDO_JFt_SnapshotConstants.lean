import NDO_JFt_SnapshotHeader
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotConstants
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def formatArray : Array U8 32#usize :=
  ⟨JFt_SnapshotHeader.format.val,by simp [JFt_SnapshotHeader.format,JFu_PublicMeta01.bytes]⟩

theorem format_call : POOL_V1_PAIR_TREE_FORMAT_BINDING=ok formatArray := by
  obtain ⟨z,add,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=20#usize) (y:=1#usize) (by scalar_tac))
  have same : z=21#usize := by scalar_tac
  rw [same] at add
  unfold POOL_V1_PAIR_TREE_FORMAT_BINDING POOL_V1_PAIR_NOTE_DEPTH
    POOL_V1_PAIR_TREE_DEPTH POOL_V1_PAIR_SECOND_SENTINEL_LANE
    pool_v1.format.POOL_V1_TREE_DEPTH POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
  have c20 : UScalar.cast .U8 20#usize=20#u8 := by scalar_tac
  have c21 : UScalar.cast .U8 21#usize=21#u8 := by scalar_tac
  have c7 : UScalar.cast .U8 7#usize=7#u8 := by scalar_tac
  simp only [add,lift,bind_tc_ok,c20,c21,c7]
  rfl

theorem magic_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC {start:=0#usize,«end»:=8#usize}=ok JFt_SnapshotHeader.magic := by
  unfold POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
  rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
    JFt_SnapshotHeader.magic JFt_SnapshotHeader.magic=ok false := by rfl

theorem format_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    formatArray {start:=0#usize,«end»:=32#usize}=ok JFt_SnapshotHeader.format := by rfl

theorem format_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
    JFt_SnapshotHeader.format JFt_SnapshotHeader.format=ok false := by rfl

#print axioms format_call
#print axioms magic_array
#print axioms magic_compare
#print axioms format_array
#print axioms format_compare
end AspisR1.JFt_SnapshotConstants

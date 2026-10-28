import NBK_LatePreflight
import NBK_AfterstateResult
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBN_LatePrepare
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def run {T : Type} (output : Slice U8) (k : Slice U8 → Result T) : Result T := do
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output { «end» := 8#usize }
      let s1 ← lift (Array.to_slice pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
      let output4 ← Slice.update output3 9#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 10#usize, «end» := 12#usize }
      let i2 ← lift (UScalar.cast .U16 pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES)
      let a ← lift (core.num.U16.to_le_bytes i2)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output5 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 12#usize, «end» := 16#usize }
      let i3 ← lift (UScalar.cast .U32 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)
      let a1 ← lift (core.num.U32.to_le_bytes i3)
      let s7 ← lift (Array.to_slice a1)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output6 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 16#usize, «end» := 20#usize }
      let i4 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
      let i5 ← lift (UScalar.cast .U32 i4)
      let a2 ← lift (core.num.U32.to_le_bytes i5)
      let s10 ← lift (Array.to_slice a2)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output7 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 20#usize, «end» := 24#usize }
      let i6 ← lift (UScalar.cast .U32 1520#usize)
      let a3 ← lift (core.num.U32.to_le_bytes i6)
      let s13 ← lift (Array.to_slice a3)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output8 := index_mut_back4 s14
      k output8

def value (output : Slice U8) : Slice U8 :=
  ⟨((((((output.val.setSlice! 0 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val).set
    8 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION).set
    9 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT).setSlice!
    10 (core.num.U16.to_le_bytes 32#u16).val).setSlice!
    12 (core.num.U32.to_le_bytes 800#u32).val).setSlice!
    16 (core.num.U32.to_le_bytes 688#u32).val).setSlice!
    20 (core.num.U32.to_le_bytes 1520#u32).val, by
      simpa only [List.length_setSlice!,List.length_set] using output.property⟩

theorem exact {T : Type} (output : Slice U8) (size : output.length = 1520)
    (k : Slice U8 → Result T) : run output k = k (value output) := by
  have len : output.val.length = 1520 := size
  have afterSize : pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES = ok 688#usize := by
    unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    exact Scalar.add_eq 8#usize 680#usize 688#usize (by scalar_tac)
  have cast16 : UScalar.cast .U16 32#usize = 32#u16  := by scalar_tac
  have cast800 : UScalar.cast .U32 800#usize = 800#u32  := by scalar_tac
  have cast688 : UScalar.cast .U32 688#usize = 688#u32  := by scalar_tac
  have cast1520 : UScalar.cast .U32 1520#usize = 1520#u32  := by scalar_tac
  unfold run
  simp only [AspisR1.JFs_LateConstants.size,bind_tc_ok,lift]
  simp [afterSize,cast16,cast800,cast688,cast1520, core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice,core.slice.Slice.copy_from_slice,
    Slice.length,Slice.len,Slice.update,len,List.slice,value,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,
    POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]

#print axioms exact
end NBN_LatePrepare

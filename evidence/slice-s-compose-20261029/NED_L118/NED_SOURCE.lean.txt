import NED_LateCarrierFields
import NED_RawLateFactor
set_option autoImplicit false
namespace NED_RawLatePrepare
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct.aspis_statement

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

theorem source {T : Type} (out : Slice U8) (k : Slice U8 → Result T) :
    run out k = NBN_LatePrepare.run out k := by
  unfold run NBN_LatePrepare.run
  simp only [NED_LateEncodingConstants.magic,NED_LateEncodingConstants.version,
    NED_LateEncodingConstants.items,NED_LateEncodingConstants.header,
    NED_LateEncodingConstants.live_bytes,NED_LateEncodingConstants.after_bytes]

theorem exact {T : Type} (out : Slice U8) (size : out.length = 1520)
    (k : Slice U8 → Result T) : run out k = k (NBN_LatePrepare.value out) :=
  (source out k).trans (NBN_LatePrepare.exact out size k)

#print axioms source
#print axioms exact
end NED_RawLatePrepare

import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_D188_Context
structure aspis_core.state_only_hiding.StateOnlyHidingContext where
  statement_digest : Array Std.U8 32#usize
  mask_nonce : Array Std.U8 32#usize
  mask_layout_fingerprint : Std.U64
  layout_factor_fingerprint : Std.U64


-- Frozen native constant state_only_hiding.rs:97; not an opaque callback.
def aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION : Result U8 := ok 1#u8
def aspis_core.state_only_hiding.StateOnlyHidingContext.encode
  (self : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  Result (Array Std.U8 81#usize)
  := do
  let encoded := Array.repeat 81#usize 0#u8
  let i ← aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION
  let encoded1 ← Array.update encoded 0#usize i
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded1
      { start := 1#usize, «end» := 33#usize }
  let s1 ← lift (Array.to_slice self.statement_digest)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let encoded2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded2
      { start := 33#usize, «end» := 65#usize }
  let s4 ← lift (Array.to_slice self.mask_nonce)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let encoded3 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded3
      { start := 65#usize, «end» := 73#usize }
  let a ← lift (core.num.U64.to_le_bytes self.mask_layout_fingerprint)
  let s7 ← lift (Array.to_slice a)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let encoded4 := index_mut_back2 s8
  let (s9, index_mut_back3) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded4
      { start := 73#usize, «end» := 81#usize }
  let a1 ← lift (core.num.U64.to_le_bytes self.layout_factor_fingerprint)
  let s10 ← lift (Array.to_slice a1)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  ok (index_mut_back3 s11)


#eval (do let v ← aspis_core.state_only_hiding.StateOnlyHidingContext.encode
            {statement_digest := Array.repeat 32#usize 2#u8,
             mask_nonce := Array.repeat 32#usize 3#u8,
             mask_layout_fingerprint := 4#u64,layout_factor_fingerprint := 5#u64}
          ok (v.val.map (fun x => x.val)) : Result (List Nat))

end PV_D188_Context

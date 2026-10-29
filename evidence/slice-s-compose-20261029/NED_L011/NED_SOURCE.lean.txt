import NBP_CommonTail1
import NBP_ArrayIndex
import NBP_Store
import NBG_Header
set_option autoImplicit false
noncomputable section
namespace NBP_CommonTail0
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (common : C) : Result (Array U8 216#usize) := do
  let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output { «end» := 4#usize }
  let s1 ← lift (Array.to_slice magic)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output1 := index_mut_back s2
  let output2 ← Array.update output1 4#usize pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION
  let kind1 := read_discriminant kind
  let i ← lift (UScalar.cast .U8 kind1)
  let output3 ← Array.update output2 5#usize i
  let output4 ← Array.update output3 6#usize pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  NBP_CommonTail1.run output4 common

def expected (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (common : C) : Array U8 216#usize :=
  let output := output.setSlice! 0 magic.val
  let output := output.set 4#usize 1#u8
  let output := output.set 5#usize (NBG_Header.tag kind)
  let output := output.set 6#usize 1#u8
  NBP_CommonTail1.expected output common

theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (common : C) : run output magic kind common = ok (expected output magic kind common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NBP_ArrayIndex.prefix_index output 4#usize (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NBP_ArrayIndex.slice output 0#usize 4#usize) magic.to_slice
    _) = _
  rw [NBP_ArrayIndex.copy_range output 0#usize 4#usize magic (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.update _ 4#usize 1#u8 (by decide),bind_tc_ok]
  rw [NBP_Store.update _ 5#usize (NBG_Header.tag kind) (by decide),bind_tc_ok]
  rw [NBP_Store.update _ 6#usize 1#u8 (by decide),bind_tc_ok]
  rw [NBP_CommonTail1.result]
  rfl
#print axioms result
end NBP_CommonTail0

import NBP_CommonTail5
import NBP_ArrayIndex
import NBP_Store
import NBG_Header
set_option autoImplicit false
noncomputable section
namespace NBP_CommonTail4
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s12, index_mut_back4) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET, «end» := pool_v1.payment_relation.NULLIFIER_OFFSET }
  let a1 ← atomic_statement.encode_digest_canonical common.anchor_root
  let s13 ← lift (Array.to_slice a1)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let output8 := index_mut_back4 s14
  NBP_CommonTail5.run output8 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NBP_CommonTail5.expected (output.setSlice! 80 (AspisR1.S2K.DigestBytes.bytes common.anchor_root).val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NBP_ArrayIndex.index_mut output 80#usize 112#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NBP_ArrayIndex.slice output 80#usize 112#usize) (AspisR1.S2K.DigestBytes.bytes common.anchor_root).to_slice
    _) = _
  rw [NBP_ArrayIndex.copy_range output 80#usize 112#usize (AspisR1.S2K.DigestBytes.bytes common.anchor_root) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_CommonTail5.result]
  rfl
#print axioms result
end NBP_CommonTail4

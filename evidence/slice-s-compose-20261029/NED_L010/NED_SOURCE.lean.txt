import NBP_CommonTail2
import NBP_ArrayIndex
import NBP_Store
import NBG_Header
set_option autoImplicit false
noncomputable section
namespace NBP_CommonTail1
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s3, index_mut_back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.POOL_OFFSET, «end» := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET }
  let s4 ← lift (Array.to_slice common.pool)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output5 := index_mut_back1 s5
  NBP_CommonTail2.run output5 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NBP_CommonTail2.expected (output.setSlice! 8 common.pool.val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NBP_ArrayIndex.index_mut output 8#usize 40#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NBP_ArrayIndex.slice output 8#usize 40#usize) common.pool.to_slice
    _) = _
  rw [NBP_ArrayIndex.copy_range output 8#usize 40#usize common.pool (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_CommonTail2.result]
  rfl
#print axioms result
end NBP_CommonTail1

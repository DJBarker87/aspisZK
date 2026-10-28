import NBP_CommonTail3
import NBP_ArrayIndex
import NBP_Store
import NBG_Header
set_option autoImplicit false
noncomputable section
namespace NBP_CommonTail2
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s6, index_mut_back2) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET, «end» := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET }
  let s7 ← lift (Array.to_slice common.deployment_domain)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let output6 := index_mut_back2 s8
  NBP_CommonTail3.run output6 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NBP_CommonTail3.expected (output.setSlice! 40 common.deployment_domain.val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NBP_ArrayIndex.index_mut output 40#usize 72#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NBP_ArrayIndex.slice output 40#usize 72#usize) common.deployment_domain.to_slice
    _) = _
  rw [NBP_ArrayIndex.copy_range output 40#usize 72#usize common.deployment_domain (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_CommonTail3.result]
  rfl
#print axioms result
end NBP_CommonTail2

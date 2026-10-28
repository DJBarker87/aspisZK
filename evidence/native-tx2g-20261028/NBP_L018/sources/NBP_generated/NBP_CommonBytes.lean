import NBP_DigestEncode
import NBG_Header
set_option autoImplicit false
noncomputable section
namespace NBP_CommonBytes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
/-- Exact write sequence; byte7 and the suffix148..216 retain their pre-state. -/
def encoded (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (c : C) :
    Array U8 216#usize :=
  ((((((((output.setSlice! 0 magic.val).setSlice! 4 [1#u8]).setSlice! 5 [NBG_Header.tag kind]).setSlice! 6 [1#u8])
    .setSlice! 8 c.pool.val).setSlice! 40 c.deployment_domain.val)
    .setSlice! 72 (core.num.U64.to_le_bytes c.anchor_sequence).val)
    .setSlice! 80 (AspisR1.S2K.DigestBytes.bytes c.anchor_root).val)
    .setSlice! 112 (AspisR1.S2K.DigestBytes.bytes c.nullifier).val)
    .setSlice! 144 (core.num.U32.to_le_bytes c.asset_id).val

theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c = ok (encoded output magic kind c) := by
  simp [pool_v1.payment_relation.encode_common,
    pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,Slice.len,Slice.length,
    Array.from_slice,Array.update,output.property,magic.property,c.pool.property,c.deployment_domain.property,
    aspis_core.field.M31.to_le_bytes,encoded,lift,bind_tc_ok]
#print axioms result
end NBP_CommonBytes

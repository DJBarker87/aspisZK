import NBP_DigestEncode
import NBG_Header
import NBP_PrefixStore
import NBP_BindPair
set_option autoImplicit false
noncomputable section
namespace NBP_CommonBytes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
/-- Exact write sequence; byte7 and the suffix148..216 retain their pre-state. -/
def encoded (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (c : C) :
    Array U8 216#usize :=
  let o := output.setSlice! 0 magic.val
  let o := o.set 4#usize 1#u8
  let o := o.set 5#usize (NBG_Header.tag kind)
  let o := o.set 6#usize 1#u8
  let o := o.setSlice! 8 c.pool.val
  let o := o.setSlice! 40 c.deployment_domain.val
  let o := o.setSlice! 72 (core.num.U64.to_le_bytes c.anchor_sequence).val
  let o := o.setSlice! 80 (AspisR1.S2K.DigestBytes.bytes c.anchor_root).val
  let o := o.setSlice! 112 (AspisR1.S2K.DigestBytes.bytes c.nullifier).val
  o.setSlice! 144 (core.num.U32.to_le_bytes c.asset_id).val

def action (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) : Result (Array U8 216#usize) := do
  let o ← NBP_Store.store output 0#usize 4#usize magic
  let o ← o.update 4#usize 1#u8
  let o ← o.update 5#usize (NBG_Header.tag kind)
  let o ← o.update 6#usize 1#u8
  let o ← NBP_Store.store o 8#usize 40#usize c.pool
  let o ← NBP_Store.store o 40#usize 72#usize c.deployment_domain
  let o ← NBP_Store.store o 72#usize 80#usize (core.num.U64.to_le_bytes c.anchor_sequence)
  let o ← NBP_Store.store o 80#usize 112#usize (AspisR1.S2K.DigestBytes.bytes c.anchor_root)
  let o ← NBP_Store.store o 112#usize 144#usize (AspisR1.S2K.DigestBytes.bytes c.nullifier)
  NBP_Store.store o 144#usize 148#usize (core.num.U32.to_le_bytes c.asset_id)

theorem action_result (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) : action output magic kind c = ok (encoded output magic kind c) := by
  unfold action
  rw [NBP_Store.exact _ 0#usize 4#usize magic (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.update _ 4#usize 1#u8 (by decide),bind_tc_ok]
  rw [NBP_Store.update _ 5#usize (NBG_Header.tag kind) (by decide),bind_tc_ok]
  rw [NBP_Store.update _ 6#usize 1#u8 (by decide),bind_tc_ok]
  rw [NBP_Store.exact _ 8#usize 40#usize c.pool (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.exact _ 40#usize 72#usize c.deployment_domain (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.exact _ 72#usize 80#usize (core.num.U64.to_le_bytes c.anchor_sequence) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.exact _ 80#usize 112#usize (AspisR1.S2K.DigestBytes.bytes c.anchor_root) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.exact _ 112#usize 144#usize (AspisR1.S2K.DigestBytes.bytes c.nullifier) (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NBP_Store.exact _ 144#usize 148#usize (core.num.U32.to_le_bytes c.asset_id) (by decide) (by decide) (by decide)]
  rfl

theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c = ok (encoded output magic kind c) := by
  rw [← action_result]
  unfold pool_v1.payment_relation.encode_common
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  simp only [action,NBP_Store.store,bind_assoc_eq,NBP_BindPair.cases_bind,lift,bind_tc_ok]
  simp only [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
  simp only [bind_assoc_eq,NBP_BindPair.cases_bind,bind_tc_ok]
  rfl
#print axioms action_result
#print axioms result
end NBP_CommonBytes

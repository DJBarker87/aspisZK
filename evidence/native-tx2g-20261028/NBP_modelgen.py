from pathlib import Path
P=Path('lean')
s='''import NBP_CommonBytes
import NBP_CommonDecode
import NBG_PaymentValidators
set_option autoImplicit false
noncomputable section
namespace NBP_PaymentModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev T := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def transfer_bytes (p : T) : Array U8 216#usize :=
  ((NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
    pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer
    (NBG_PaymentValidators.tc p)).setSlice! 152 (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).val)
    .setSlice! 184 (AspisR1.S2K.DigestBytes.bytes p.change_commitment).val

def withdrawal_bytes (p : W) : Array U8 216#usize :=
  (((NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
    pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal
    (NBG_PaymentValidators.wc p)).setSlice! 148 (core.num.U32.to_le_bytes p.amount).val)
    .setSlice! 152 p.destination_token_account.val)
    .setSlice! 184 (AspisR1.S2K.DigestBytes.bytes p.change_commitment).val

def transfer_encoded (p : T) : core.result.Result (Array U8 216#usize) E :=
  match NBG_PaymentValidators.transfer p with
  | .Err e => .Err e | .Ok () => .Ok (transfer_bytes p)
def withdrawal_encoded (p : W) : core.result.Result (Array U8 216#usize) E :=
  match NBG_PaymentValidators.withdrawal p with
  | .Err e => .Err e | .Ok () => .Ok (withdrawal_bytes p)

def transfer_public (c : C) (r z : Array U32 8#usize) : T :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id,r,z⟩
def withdrawal_public (c : C) (b : Array U8 216#usize) (z : Array U32 8#usize) : W :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id,
    core.num.U32.from_le_bytes (NBP_Read.chunk b 148 (by decide)),
    NBP_Read.chunk b 152 (by decide),z⟩

def transfer_decoded (b : Array U8 216#usize) : core.result.Result T E :=
  match NBG_Header.expected b pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer with
  | .Err e => .Err e
  | .Ok () =>
    if (b.val.drop 148).take 4 ≠ List.replicate 4 0#u8 then .Err .NonZeroReserved else
    match NBP_CommonDecode.decoded b with
    | .Err e => .Err e
    | .Ok c =>
      match NBP_DigestDecode.decoded (NBP_Read.chunk b 152 (by decide)) with
      | .Err _ => .Err .NonCanonicalDigest
      | .Ok r =>
        match NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
        | .Err _ => .Err .NonCanonicalDigest
        | .Ok z =>
          let p := transfer_public c r z
          match NBG_PaymentValidators.transfer p with
          | .Err e => .Err e | .Ok () => .Ok p

def withdrawal_decoded (b : Array U8 216#usize) : core.result.Result W E :=
  match NBG_Header.expected b pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal with
  | .Err e => .Err e
  | .Ok () =>
    match NBP_CommonDecode.decoded b with
    | .Err e => .Err e
    | .Ok c =>
      match NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
      | .Err _ => .Err .NonCanonicalDigest
      | .Ok z =>
        let p := withdrawal_public c b z
        match NBG_PaymentValidators.withdrawal p with
        | .Err e => .Err e | .Ok () => .Ok p
end NBP_PaymentModel
'''
(P/'NBP_PaymentModel.lean').write_text(s)
# Use the same exact normalization as the passing common decoder, leaving
# closed callee specifications opaque and splitting only Result/control tags.
base=Path('lean/NBP_CommonDecode.lean').read_text();t=base[base.index('  simp [pool_v1.payment_relation.decode_common,'):base.index('#print axioms result')]
for kind in ['Transfer','Withdrawal']:
 fun='decode_pool_v1_'+('private_transfer' if kind=='Transfer' else 'withdrawal')+'_public_v1';name='NBP_'+kind+'Decode';model=kind.lower()+'_decoded';typ='T' if kind=='Transfer' else 'W'
 tt=t.replace('pool_v1.payment_relation.decode_common,',f'pool_v1.payment_relation.{fun},\n    NBG_Header.header_result,NBP_CommonDecode.result,NBG_PaymentValidators.'+kind.lower()+'_result,')
 tt=tt.replace('pool_v1.payment_relation.decode_common.closure',f'pool_v1.payment_relation.{fun}.closure')
 tt=tt.replace('asset,common,decoded,NBP_Read.chunk',f'{model},'+kind.lower()+'_public,NBP_Read.chunk')
 tt=tt.replace('    core.result.Result.map_err,','''    pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
    pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    pool_v1.payment_relation.POOL_V1_CANONICAL_FEE,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,NBG_Header.slice_equal,
    core.result.Result.map_err,''')
 # length-error map closure has a different argument type.
 tt=tt.replace(fun+'.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError',fun+'.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError')
 if kind=='Transfer':
  path=f'pool_v1.payment_relation.{fun}.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError'
  tt=tt.replace('    core.result.Result.Insts.CoreOpsTry.branch,',f'    {path},{path}.call_once,\n    core.result.Result.Insts.CoreOpsTry.branch,')
 tt=tt.replace('Array.to_slice,Slice.length,Slice.len,b.property','Array.to_slice,Slice.length,Slice.len,b.property')
 out=f'''import NBP_PaymentModel
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_PaymentModel

theorem fixed (b : Array U8 216#usize) :
    pool_v1.payment_relation.{fun} b.to_slice = ok ({model} b) := by
'''+tt+f'\n#print axioms fixed\nend {name}\n'
 (P/(name+'.lean')).write_text(out)
# Independent full-Result encoder proofs, composing only closed callees.
for kind in ['Transfer','Withdrawal']:
 name='NBP_'+kind+'Encode';lower=kind.lower();fun='encode_pool_v1_'+('private_transfer' if kind=='Transfer' else 'withdrawal')+'_public_v1';typ='T' if kind=='Transfer' else 'W';validator='validate_pool_v1_'+('private_transfer' if kind=='Transfer' else 'withdrawal')+'_public_v1'
 s=f'''import NBP_PaymentModel
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_PaymentModel

theorem result (p : {typ}) : pool_v1.payment_relation.{fun} p = ok ({lower}_encoded p) := by
  simp only [pool_v1.payment_relation.{fun},NBG_PaymentValidators.{lower}_result,
    {lower}_encoded,bind_tc_ok]
  cases h : NBG_PaymentValidators.{lower} p with
  | Err e =>
    simp [h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [NBG_Atomic.{lower}_projection]
    simp only [bind_tc_ok]
    rw [NBP_CommonBytes.result]
    simp only [bind_tc_ok,NBP_DigestEncode.result,lift,
      pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    unfold {lower}_bytes
'''
 magic='PRIVATE_TRANSFER' if kind=='Transfer' else 'WITHDRAWAL';tag='PrivateTransfer' if kind=='Transfer' else 'Withdrawal';cp='tc' if kind=='Transfer' else 'wc'
 expr=f'NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8) pool_v1.payment_relation.POOL_V1_{magic}_STATEMENT_MAGIC .{tag} (NBG_PaymentValidators.{cp} p)'
 s+=f'    generalize h0 : {expr} = o0\n'
 rows=[(152,184,'(AspisR1.S2K.DigestBytes.bytes p.recipient_commitment)')] if kind=='Transfer' else [(148,152,'(core.num.U32.to_le_bytes p.amount)'),(152,184,'p.destination_token_account')]
 for i,(start,stop,expr) in enumerate(rows):
  out=f'o{i}'
  s+=f'''    rw [NBP_ArrayIndex.index_mut {out} {start}#usize {stop}#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice {out} {start}#usize {stop}#usize) {expr}.to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range {out} {start}#usize {stop}#usize {expr} (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok]
    generalize h{i+1} : {out}.setSlice! {start} {expr}.val = o{i+1}
'''
 out=f'o{len(rows)}';expr='(AspisR1.S2K.DigestBytes.bytes p.change_commitment)'
 s+=f'''    rw [NBP_ArrayIndex.suffix_index {out} 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice {out} 184#usize 216#usize) {expr}.to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range {out} 184#usize 216#usize {expr} (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok]
    rfl
#print axioms result
end {name}
'''
 (P/(name+'.lean')).write_text(s)

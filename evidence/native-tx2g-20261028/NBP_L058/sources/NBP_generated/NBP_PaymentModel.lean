import NBP_CommonBytes
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
  let o := NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
    pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer
    (NBG_PaymentValidators.tc p)
  let o := o.setSlice! 152 (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).val
  o.setSlice! 184 (AspisR1.S2K.DigestBytes.bytes p.change_commitment).val

def withdrawal_bytes (p : W) : Array U8 216#usize :=
  let o := NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
    pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal
    (NBG_PaymentValidators.wc p)
  let o := o.setSlice! 148 (core.num.U32.to_le_bytes p.amount).val
  let o := o.setSlice! 152 p.destination_token_account.val
  o.setSlice! 184 (AspisR1.S2K.DigestBytes.bytes p.change_commitment).val

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

import NEQ_CommonDecode
import NBP_TransferDecode
import NBP_WithdrawalDecode
set_option autoImplicit false
noncomputable section
namespace NEQ_PaymentDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NBP_PaymentModel
attribute [local instance] Classical.propDecidable
abbrev CommonCall := Array U8 216#usize → Result (core.result.Result C E)
abbrev Decode := NEQ_CommonDecode.DigestCall
abbrev TransferCheck := T → Result (core.result.Result Unit E)
abbrev WithdrawalCheck := W → Result (core.result.Result Unit E)

def transferRun (common : CommonCall) (decode : Decode) (validate : TransferCheck)
    (b : Array U8 216#usize) : Result (core.result.Result T E) := do
  let h ← pool_v1.payment_relation.require_header b
    pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer
  match h with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    if (b.val.drop 148).take 4 ≠ List.replicate 4 0#u8 then ok (.Err .NonZeroReserved)
    else
      let c ← common b
      match c with
      | .Err e => ok (.Err e)
      | .Ok c =>
        let r ← decode (NBP_Read.chunk b 152 (by decide))
        match r with
        | .Err _ => ok (.Err .NonCanonicalDigest)
        | .Ok r =>
          let z ← decode (NBP_Read.chunk b 184 (by decide))
          match z with
          | .Err _ => ok (.Err .NonCanonicalDigest)
          | .Ok z =>
            let p := transfer_public c r z
            let valid ← validate p
            match valid with | .Err e => ok (.Err e) | .Ok _ => ok (.Ok p)

def withdrawalRun (common : CommonCall) (decode : Decode) (validate : WithdrawalCheck)
    (b : Array U8 216#usize) : Result (core.result.Result W E) := do
  let h ← pool_v1.payment_relation.require_header b
    pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal
  match h with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let c ← common b
    match c with
    | .Err e => ok (.Err e)
    | .Ok c =>
      let z ← decode (NBP_Read.chunk b 184 (by decide))
      match z with
      | .Err _ => ok (.Err .NonCanonicalDigest)
      | .Ok z =>
        let p := withdrawal_public c b z
        let valid ← validate p
        match valid with | .Err e => ok (.Err e) | .Ok _ => ok (.Ok p)

theorem transfer_substitution (b : Array U8 216#usize) :
    transferRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 b =
      ok (transfer_decoded b) := by
  unfold transferRun transfer_decoded
  simp only [NBG_Header.header_result,NBP_CommonDecode.result,NBP_DigestDecode.result,
    NBG_PaymentValidators.transfer_result,bind_tc_ok]
  cases h : NBG_Header.expected b pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer with
  | Err e => rfl
  | Ok u =>
    dsimp only
    by_cases fee : (b.val.drop 148).take 4 ≠ List.replicate 4 0#u8
    · simp only [if_pos fee]
    · simp only [if_neg fee]
      cases c : NBP_CommonDecode.decoded b with
      | Err e => rfl
      | Ok common =>
        dsimp only
        cases r : NBP_DigestDecode.decoded (NBP_Read.chunk b 152 (by decide)) with
        | Err e => rfl
        | Ok recipient =>
          dsimp only
          cases z : NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
          | Err e => rfl
          | Ok change =>
            dsimp only
            cases NBG_PaymentValidators.transfer (transfer_public common recipient change) <;> rfl

theorem withdrawal_substitution (b : Array U8 216#usize) :
    withdrawalRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 b =
      ok (withdrawal_decoded b) := by
  unfold withdrawalRun withdrawal_decoded
  simp only [NBG_Header.header_result,NBP_CommonDecode.result,NBP_DigestDecode.result,
    NBG_PaymentValidators.withdrawal_result,bind_tc_ok]
  cases h : NBG_Header.expected b pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal with
  | Err e => rfl
  | Ok u =>
    dsimp only
    cases c : NBP_CommonDecode.decoded b with
    | Err e => rfl
    | Ok common =>
      dsimp only
      cases z : NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
      | Err e => rfl
      | Ok change =>
        dsimp only
        cases NBG_PaymentValidators.withdrawal (withdrawal_public common b change) <;> rfl

def transferFull (bytes : Slice U8) : Result (core.result.Result T E) :=
  if h : bytes.val.length=216 then
    transferRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 ⟨bytes.val,h⟩
  else ok (.Err .WrongLength)

def withdrawalFull (bytes : Slice U8) : Result (core.result.Result W E) :=
  if h : bytes.val.length=216 then
    withdrawalRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 ⟨bytes.val,h⟩
  else ok (.Err .WrongLength)

theorem transfer_result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (transferFull bytes,state,([] : List Unit)) =
      (pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 bytes,state,[]) := by
  unfold transferFull
  rw [NBP_TransferDecode.result]
  by_cases h : bytes.val.length=216
  · rw [dif_pos h,dif_pos h,transfer_substitution]
  · rw [dif_neg h,dif_neg h]

theorem withdrawal_result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (withdrawalFull bytes,state,([] : List Unit)) =
      (pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes,state,[]) := by
  unfold withdrawalFull
  rw [NBP_WithdrawalDecode.result]
  by_cases h : bytes.val.length=216
  · rw [dif_pos h,dif_pos h,withdrawal_substitution]
  · rw [dif_neg h,dif_neg h]

#print axioms transfer_substitution
#print axioms withdrawal_substitution
#print axioms transfer_result_state_effects
#print axioms withdrawal_result_state_effects
end NEQ_PaymentDecode

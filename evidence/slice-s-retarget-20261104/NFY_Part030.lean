import Lean
import NFY_Part029
import NFY_Part005
import NFY_Part028
import NFY_Part025

-- BEGIN copied NBP_CommonTail1: lean/NBP_CommonTail1.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail1
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind

def run (output : Array U8 216#usize) (common : C) : Result (Array U8 216#usize) := do
  let (s3, index_mut_back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output { start := pool_v1.payment_relation.POOL_OFFSET, «end» := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET }
  let s4 ← lift (Array.to_slice common.pool)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output5 := index_mut_back1 s5
  NFY_NBP_CommonTail2.run output5 common

def expected (output : Array U8 216#usize) (common : C) : Array U8 216#usize :=
  NFY_NBP_CommonTail2.expected (output.setSlice! 8 common.pool.val) common

theorem result (output : Array U8 216#usize) (common : C) : run output common = ok (expected output common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.index_mut output 8#usize 40#usize (by decide) (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 8#usize 40#usize) common.pool.to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 8#usize 40#usize common.pool (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NFY_NBP_CommonTail2.result]
  rfl
#print axioms result
end NFY_NBP_CommonTail1
-- END copied NBP_CommonTail1
-- BEGIN copied NBP_CommonTail0: lean/NBP_CommonTail0.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonTail0
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
  NFY_NBP_CommonTail1.run output4 common

def expected (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (common : C) : Array U8 216#usize :=
  let output := output.setSlice! 0 magic.val
  let output := output.set 4#usize 1#u8
  let output := output.set 5#usize (NFY_NBG_Header.tag kind)
  let output := output.set 6#usize 1#u8
  NFY_NBP_CommonTail1.expected output common

theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (common : C) : run output magic kind common = ok (expected output magic kind common) := by
  unfold run
  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NFY_NBP_DigestEncode.result,NFY_NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
  rw [NFY_NBP_ArrayIndex.prefix_index output 4#usize (by decide)]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NFY_NBP_ArrayIndex.slice output 0#usize 4#usize) magic.to_slice
    _) = _
  rw [NFY_NBP_ArrayIndex.copy_range output 0#usize 4#usize magic (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
  rw [NFY_NBP_Store.update _ 4#usize 1#u8 (by decide),bind_tc_ok]
  rw [NFY_NBP_Store.update _ 5#usize (NFY_NBG_Header.tag kind) (by decide),bind_tc_ok]
  rw [NFY_NBP_Store.update _ 6#usize 1#u8 (by decide),bind_tc_ok]
  rw [NFY_NBP_CommonTail1.result]
  rfl
#print axioms result
end NFY_NBP_CommonTail0
-- END copied NBP_CommonTail0
-- BEGIN copied NBP_CommonBytes: lean/NBP_CommonBytes.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonBytes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
abbrev encoded := NFY_NBP_CommonTail0.expected

theorem association (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c =
      NFY_NBP_CommonTail0.run output magic kind c := by
  unfold pool_v1.payment_relation.encode_common
  unfold NFY_NBP_CommonTail0.run NFY_NBP_CommonTail1.run NFY_NBP_CommonTail2.run NFY_NBP_CommonTail3.run NFY_NBP_CommonTail4.run NFY_NBP_CommonTail5.run NFY_NBP_CommonTail6.run
  rfl
theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c = ok (encoded output magic kind c) := by
  rw [association]
  exact NFY_NBP_CommonTail0.result output magic kind c
#print axioms association
#print axioms result
end NFY_NBP_CommonBytes
-- END copied NBP_CommonBytes
-- BEGIN copied NBG_PaymentValidators: lean/NBG_PaymentValidators.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBG_PaymentValidators
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NFY_NBG_PaymentChecks
abbrev T := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := pool_v1.payment_relation.PoolV1WithdrawalPublicV1

def tc (p : T) : C :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id }
def wc (p : W) : C :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id }

def transfer (p : T) : core.result.Result Unit E :=
  match common (tc p) with
  | .Err e => .Err e
  | .Ok () => if !canonical p.recipient_commitment || !canonical p.change_commitment
      then .Err .NonCanonicalDigest else .Ok ()

theorem transfer_result (p : T) :
    pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 p =
      ok (transfer p) := by
  have projected : pool_v1.payment_relation.transfer_common p = ok (tc p) :=
    NBG_Atomic.transfer_projection p
  unfold pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
  rw [projected,bind_tc_ok,common_result,bind_tc_ok]
  cases h : common (tc p) with
  | Err e => simp [transfer,h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok value => cases value; simp [transfer,h,canonical_result,
      core.result.Result.Insts.CoreOpsTry.branch]
                repeat' split
                all_goals simp_all

theorem value_limit : spend.VALUE_LIMIT = ok 1073741824#u32 := by
  unfold spend.VALUE_LIMIT
  rfl

def withdrawal (p : W) : core.result.Result Unit E :=
  match common (wc p) with
  | .Err e => .Err e
  | .Ok () => if p.amount.val = 0 ∨ p.amount.val >= 1073741824
      then .Err .InvalidWithdrawalAmount
      else if zero p.destination_token_account then .Err .InvalidDestination
      else if !canonical p.change_commitment then .Err .NonCanonicalDigest
      else .Ok ()

theorem withdrawal_result (p : W) :
    pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p =
      ok (withdrawal p) := by
  have projected : pool_v1.payment_relation.withdrawal_common p = ok (wc p) :=
    NBG_Atomic.withdrawal_projection p
  unfold pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
  rw [projected,bind_tc_ok,common_result,bind_tc_ok]
  cases h : common (wc p) with
  | Err e => simp [withdrawal,h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok value => cases value; simp [withdrawal,h,canonical_result,zero_result,value_limit,
      core.result.Result.Insts.CoreOpsTry.branch]
                repeat' split
                all_goals simp_all <;> scalar_tac

#print axioms transfer_result
#print axioms value_limit
#print axioms withdrawal_result
end NFY_NBG_PaymentValidators
-- END copied NBG_PaymentValidators
-- BEGIN copied NBP_PaymentModel: lean/NBP_PaymentModel.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_PaymentModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev T := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def transfer_bytes (p : T) : Array U8 216#usize :=
  let o := NFY_NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
    pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer
    (NFY_NBG_PaymentValidators.tc p)
  let o := o.setSlice! 152 (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).val
  o.setSlice! 184 (AspisR1.S2K.DigestBytes.bytes p.change_commitment).val

def withdrawal_bytes (p : W) : Array U8 216#usize :=
  let o := NFY_NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
    pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal
    (NFY_NBG_PaymentValidators.wc p)
  let o := o.setSlice! 148 (core.num.U32.to_le_bytes p.amount).val
  let o := o.setSlice! 152 p.destination_token_account.val
  o.setSlice! 184 (AspisR1.S2K.DigestBytes.bytes p.change_commitment).val

def transfer_encoded (p : T) : core.result.Result (Array U8 216#usize) E :=
  match NFY_NBG_PaymentValidators.transfer p with
  | .Err e => .Err e | .Ok () => .Ok (transfer_bytes p)
def withdrawal_encoded (p : W) : core.result.Result (Array U8 216#usize) E :=
  match NFY_NBG_PaymentValidators.withdrawal p with
  | .Err e => .Err e | .Ok () => .Ok (withdrawal_bytes p)

def transfer_public (c : C) (r z : Array U32 8#usize) : T :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id,r,z⟩
def withdrawal_public (c : C) (b : Array U8 216#usize) (z : Array U32 8#usize) : W :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id,
    core.num.U32.from_le_bytes (NBP_Read.chunk b 148 (by decide)),
    NBP_Read.chunk b 152 (by decide),z⟩

def transfer_decoded (b : Array U8 216#usize) : core.result.Result T E :=
  match NFY_NBG_Header.expected b pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer with
  | .Err e => .Err e
  | .Ok () =>
    if (b.val.drop 148).take 4 ≠ List.replicate 4 0#u8 then .Err .NonZeroReserved else
    match NFY_NBP_CommonDecode.decoded b with
    | .Err e => .Err e
    | .Ok c =>
      match NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 152 (by decide)) with
      | .Err _ => .Err .NonCanonicalDigest
      | .Ok r =>
        match NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
        | .Err _ => .Err .NonCanonicalDigest
        | .Ok z =>
          let p := transfer_public c r z
          match NFY_NBG_PaymentValidators.transfer p with
          | .Err e => .Err e | .Ok () => .Ok p

def withdrawal_decoded (b : Array U8 216#usize) : core.result.Result W E :=
  match NFY_NBG_Header.expected b pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal with
  | .Err e => .Err e
  | .Ok () =>
    match NFY_NBP_CommonDecode.decoded b with
    | .Err e => .Err e
    | .Ok c =>
      match NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
      | .Err _ => .Err .NonCanonicalDigest
      | .Ok z =>
        let p := withdrawal_public c b z
        match NFY_NBG_PaymentValidators.withdrawal p with
        | .Err e => .Err e | .Ok () => .Ok p
end NFY_NBP_PaymentModel
-- END copied NBP_PaymentModel
-- BEGIN copied NBP_TransferEncode: lean/NBP_TransferEncode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_TransferEncode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_PaymentModel

theorem result (p : T) : pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p = ok (transfer_encoded p) := by
  simp only [pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1,NFY_NBG_PaymentValidators.transfer_result,
    transfer_encoded,bind_tc_ok]
  cases h : NFY_NBG_PaymentValidators.transfer p with
  | Err e =>
    simp [h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    have projected : pool_v1.payment_relation.transfer_common p = ok (NFY_NBG_PaymentValidators.tc p) := NBG_Atomic.transfer_projection p
    rw [projected]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    rw [NFY_NBP_CommonBytes.result]
    simp only [bind_tc_ok,NFY_NBP_DigestEncode.result,lift,
      pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    unfold transfer_bytes
    generalize h0 : NFY_NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8) pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer (NFY_NBG_PaymentValidators.tc p) = o0
    rw [NFY_NBP_ArrayIndex.index_mut o0 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice o0 152#usize 184#usize) (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range o0 152#usize 184#usize (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize h1 : o0.setSlice! 152 (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).val = o1
    rw [NFY_NBP_ArrayIndex.suffix_index o1 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice o1 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range o1 184#usize 216#usize (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl
#print axioms result
end NFY_NBP_TransferEncode
-- END copied NBP_TransferEncode
-- BEGIN copied NBP_WithdrawalEncode: lean/NBP_WithdrawalEncode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_WithdrawalEncode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_PaymentModel

theorem result (p : W) : pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (withdrawal_encoded p) := by
  simp only [pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1,NFY_NBG_PaymentValidators.withdrawal_result,
    withdrawal_encoded,bind_tc_ok]
  cases h : NFY_NBG_PaymentValidators.withdrawal p with
  | Err e =>
    simp [h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    have projected : pool_v1.payment_relation.withdrawal_common p = ok (NFY_NBG_PaymentValidators.wc p) := NBG_Atomic.withdrawal_projection p
    rw [projected]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    rw [NFY_NBP_CommonBytes.result]
    simp only [bind_tc_ok,NFY_NBP_DigestEncode.result,lift,
      pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    unfold withdrawal_bytes
    generalize h0 : NFY_NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8) pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal (NFY_NBG_PaymentValidators.wc p) = o0
    rw [NFY_NBP_ArrayIndex.index_mut o0 148#usize 152#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice o0 148#usize 152#usize) (core.num.U32.to_le_bytes p.amount).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range o0 148#usize 152#usize (core.num.U32.to_le_bytes p.amount) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize h1 : o0.setSlice! 148 (core.num.U32.to_le_bytes p.amount).val = o1
    rw [NFY_NBP_ArrayIndex.index_mut o1 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice o1 152#usize 184#usize) p.destination_token_account.to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range o1 152#usize 184#usize p.destination_token_account (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize h2 : o1.setSlice! 152 p.destination_token_account.val = o2
    rw [NFY_NBP_ArrayIndex.suffix_index o2 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice o2 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range o2 184#usize 216#usize (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl
#print axioms result
end NFY_NBP_WithdrawalEncode
-- END copied NBP_WithdrawalEncode
-- BEGIN copied NED_CodecComposition: evidence/slice-s-compose-20261029/NED_CodecComposition.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_CodecComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- Total raw law; hence also valid at every canonical digest call site. -/
theorem digest_raw : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw
    atomic_statement.encode_digest_canonical := NFY_NBP_DigestEncode.result

theorem digest_canonical : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical
    atomic_statement.encode_digest_canonical := fun d _ => digest_raw d

/-- The safe payment reference returns the exact emitted Result on every
    typed payment, including rejection; no payment acceptance is assumed. -/
theorem transfer_law : NFY_NBN_ValidatorSummary.NBN_Dep_TransferEncode
    (fun p => ok (NFY_NBP_PaymentModel.transfer_encoded p)) :=
  fun p => (NFY_NBP_TransferEncode.result p).symm

theorem withdrawal_law : NFY_NBN_ValidatorSummary.NBN_Dep_WithdrawalEncode
    (fun p => ok (NFY_NBP_PaymentModel.withdrawal_encoded p)) :=
  fun p => (NFY_NBP_WithdrawalEncode.result p).symm

/-- Fully instantiated emitted validator composition; no inner codec premise. -/
theorem validator (s : NFY_NBN_StatementResult.Statement) :
    NFY_NBN_ValidatorSummary.run atomic_statement.encode_digest_canonical
      (fun p => ok (NFY_NBP_PaymentModel.transfer_encoded p))
      (fun p => ok (NFY_NBP_PaymentModel.withdrawal_encoded p)) s =
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s :=
  NFY_NBN_ValidatorSummary.source _ _ _ digest_canonical transfer_law withdrawal_law s

/-- Fully instantiated emitted encoder composition; exact bytes/error Result. -/
theorem encoder (s : NFY_NBN_StatementResult.Statement) :
    NFY_NBN_StatementEncoderSummary.run atomic_statement.encode_digest_canonical
      (fun p => ok (NFY_NBP_PaymentModel.transfer_encoded p))
      (fun p => ok (NFY_NBP_PaymentModel.withdrawal_encoded p)) s =
    NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s) :=
  NFY_NBN_StatementEncoderSummary.source _ _ _ digest_raw transfer_law withdrawal_law s

#print axioms digest_raw
#print axioms digest_canonical
#print axioms transfer_law
#print axioms withdrawal_law
#print axioms validator
#print axioms encoder
end NFY_NED_CodecComposition
-- END copied NED_CodecComposition
-- BEGIN copied NBN_CallbackObstruction: lean/NBN_CallbackObstruction.lean
set_option autoImplicit false
namespace NFY_NBN_CallbackObstruction
open Aeneas Aeneas.Std Result
open AspisR1

/-- Selection alone cannot determine the frozen getter's value. -/
theorem registry_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (r : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
    ∃ cFalse cTrue : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk cFalse).op25 r = ok false ∧
      (DrvC_Installation.sdk cTrue).op25 r = ok true := by
  exact ⟨{c with adapter := {c.adapter with op25 := fun _ => ok false}},
    {c with adapter := {c.adapter with op25 := fun _ => ok true}},rfl,rfl⟩

/-- No universally quantified adapter can be given a fixed op25 law from selection. -/
theorem no_fixed_registry_law {F E : Type} (c : DrvC_Installation.Configuration F E)
    (r : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1)
    (expected : Bool) :
    ¬ (∀ d : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk d).op25 r = ok expected) := by
  intro h
  obtain ⟨cf,ct,hf,ht⟩ := registry_unconstrained c r
  have ef : false = expected := Result.ok.inj (hf.symm.trans (h cf))
  have et : true = expected := Result.ok.inj (ht.symm.trans (h ct))
  cases ef.trans et.symm

#print axioms registry_unconstrained
#print axioms no_fixed_registry_law
end NFY_NBN_CallbackObstruction
-- END copied NBN_CallbackObstruction
-- BEGIN copied NBN_AccountCallbackObstruction: lean/NBN_AccountCallbackObstruction.lean
set_option autoImplicit false
namespace NFY_NBN_AccountCallbackObstruction
open Aeneas Aeneas.Std Result
open AspisR1
abbrev PE := AdapterRw.solana_program_error.ProgramError

theorem master_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (input : Slice U8)
    (m : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) :
    ∃ reject accept : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk reject).op48 input = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) ∧
      (DrvC_Installation.sdk accept).op48 input = ok (.Ok m) := by
  exact ⟨{c with adapter := {c.adapter with op48 := fun _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)}},
    {c with adapter := {c.adapter with op48 := fun _ => ok (.Ok m)}},rfl,rfl⟩

theorem checkpoint_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (input : Slice U8)
    (m : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) :
    ∃ reject accept : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk reject).op49 input = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) ∧
      (DrvC_Installation.sdk accept).op49 input = ok (.Ok m) := by
  exact ⟨{c with adapter := {c.adapter with op49 := fun _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)}},
    {c with adapter := {c.adapter with op49 := fun _ => ok (.Ok m)}},rfl,rfl⟩

theorem request_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (input : Slice U8)
    (m : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1) :
    ∃ reject accept : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk reject).op23 input =
        ok (.Err .WrongLength) ∧
      (DrvC_Installation.sdk accept).op23 input = ok (.Ok m) := by
  exact ⟨{c with adapter := {c.adapter with op23 := fun _ => ok (.Err .WrongLength)}},
    {c with adapter := {c.adapter with op23 := fun _ => ok (.Ok m)}},rfl,rfl⟩

#print axioms master_unconstrained
#print axioms checkpoint_unconstrained
#print axioms request_unconstrained
end NFY_NBN_AccountCallbackObstruction
-- END copied NBN_AccountCallbackObstruction
-- BEGIN copied NBN_U04: lean/NBN_U04.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_U04
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem conditional_helpers (enc : NFY_NBN_DigestResultDependency.Encode)
    (NBN_Dep_DigestEncodeRaw : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw enc) :
    (∀ d, NFY_NBN_FirstByteDependency.first enc d = pool_v1.pair_forest_accounts.first_canonical_byte d) ∧
    (∀ d, NFY_NBN_FirstByteDependency.lane enc d = pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d) :=
  ⟨NFY_NBN_FirstByteDependency.first_source enc NBN_Dep_DigestEncodeRaw,
    NFY_NBN_FirstByteDependency.lane_source enc (fun d _ => NBN_Dep_DigestEncodeRaw d)⟩

#print axioms conditional_helpers
end NFY_NBN_U04
-- END copied NBN_U04
-- BEGIN copied NED_SubtreeComposition: evidence/slice-s-compose-20261029/NED_SubtreeComposition.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_SubtreeComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem digest_decode : NFY_NBN_AfterDecodeTypes.NBN_Dep_DigestDecode
    (fun b => ok (NFY_NBP_DigestDecode.decoded b)) :=
  fun b => (NFY_NBP_DigestDecode.result b).symm

theorem after_encode (a : NFY_NBH_Validators.Afterstate) :
    NFY_NBN_EncoderSummary.after atomic_statement.encode_digest_canonical a =
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a :=
  NFY_NBN_EncoderSummary.after_source _ NFY_NED_CodecComposition.digest_canonical a

theorem live_encode (s : NFY_NBH_LiveValidator.Snapshot) (out : Slice U8) :
    NFY_NBN_EncoderSummary.live atomic_statement.encode_digest_canonical s out =
    pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out :=
  NFY_NBN_EncoderSummary.live_source _ NFY_NED_CodecComposition.digest_canonical s out

theorem late_encode (s : NFY_NBN_LateSummary.Statement) (out : Slice U8) :
    NFY_NBN_LateSummary.run atomic_statement.encode_digest_canonical s out =
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s out :=
  NFY_NBN_LateSummary.source _ NFY_NED_CodecComposition.digest_canonical s out

theorem after_decode (bytes : Slice U8) :
    NFY_NBN_AfterstateDecoderDependency.run (fun b => ok (NFY_NBP_DigestDecode.decoded b)) bytes =
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes :=
  NFY_NBN_AfterstateDecoderDependency.source _ digest_decode bytes

theorem first_byte (d : Array U32 8#usize) :
    NFY_NBN_FirstByteDependency.first atomic_statement.encode_digest_canonical d =
    pool_v1.pair_forest_accounts.first_canonical_byte d :=
  NFY_NBN_FirstByteDependency.first_source _ NFY_NED_CodecComposition.digest_raw d

theorem output_lane (d : Array U32 8#usize) :
    NFY_NBN_FirstByteDependency.lane atomic_statement.encode_digest_canonical d =
    pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d :=
  NFY_NBN_FirstByteDependency.lane_source _ NFY_NED_CodecComposition.digest_canonical d

#print axioms digest_decode
#print axioms after_encode
#print axioms live_encode
#print axioms late_encode
#print axioms after_decode
#print axioms first_byte
#print axioms output_lane
end NFY_NED_SubtreeComposition
-- END copied NED_SubtreeComposition
-- BEGIN copied NED_ValidatorTrace: evidence/slice-s-compose-20261029/NED_ValidatorTrace.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_ValidatorTrace
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev E := NFY_NBN_StatementResult.Error
abbrev R := Result (core.result.Result Unit E)
inductive Call where
  | payment (statement : Statement)
  | lane (nullifier : Array U32 8#usize)
  | late (argument : NFY_NBN_LateSummary.Statement) (output : Slice U8)

def enc := atomic_statement.encode_digest_canonical
def transfer (p : NFY_NBN_ValidatorSummary.Transfer) := ok (NFY_NBP_PaymentModel.transfer_encoded p)
def withdrawal (p : NFY_NBN_ValidatorSummary.Withdrawal) := ok (NFY_NBP_PaymentModel.withdrawal_encoded p)
def payment (s : Statement) := NFY_NBN_ValidatorSummary.paymentWith transfer withdrawal s

def tail (s : Statement) : R × List Call :=
  let d := (parts s).2.2.2.2.1
  match NFY_NBN_FirstByteDependency.lane enc d with
  | .fail e => (.fail e,[.lane d])
  | .div => (.div,[.lane d])
  | .ok (.Err e) => (ok (.Err (.Account e)),[.lane d])
  | .ok (.Ok l) =>
    if l ≠ (common s).output_lane then (ok (.Err .OutputLaneMismatch),[.lane d])
    else
      let arg := (common s).lane_transition
      let out := NFY_NBN_LateResult.zero
      let r : R := do
        let (status,_) ← NFY_NBN_LateSummary.run enc arg out
        match status with
        | .Err e => ok (.Err (.LaneTransition e))
        | .Ok _ => ok (.Ok ())
      (r,[.lane d,.late arg out])

def bindings (s : Statement) : R × List Call :=
  if (parts s).1 ≠ (common s).master_account then (ok (.Err .MasterBindingMismatch),[])
  else if (parts s).2.1 ≠ (common s).lane_transition.live_snapshot.deployment_domain then (ok (.Err .DeploymentBindingMismatch),[])
  else if (common s).lane_transition.live_snapshot.pool ≠ (common s).master_account then (ok (.Err .MasterBindingMismatch),[])
  else if (parts s).2.2.1 ≠ (common s).checkpoint_sequence then (ok (.Err .CheckpointBindingMismatch),[])
  else if (parts s).2.2.2.1 ≠ (common s).historical_global_anchor then (ok (.Err .HistoricalAnchorMismatch),[])
  else tail s

def run (s : Statement) : R × List Call :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then (ok (.Err .NonZeroBinding),[])
  else if 8 ≤ (common s).output_lane.val then (ok (.Err .InvalidOutputLane),[])
  else match payment s with
    | .fail e => (.fail e,[.payment s])
    | .div => (.div,[.payment s])
    | .ok (.Err e) => (ok (.Err (.Payment e)),[.payment s])
    | .ok (.Ok _) => ((bindings s).1,.payment s :: (bindings s).2)

theorem tail_erases (s : Statement) : (tail s).1 = NFY_NBN_ValidatorSummary.tail enc s := by
  unfold tail NFY_NBN_ValidatorSummary.tail
  dsimp only
  cases h : NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1 with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok r =>
    cases r with
    | Err e => simp only [h,bind_tc_ok]
    | Ok l =>
      simp only [h,bind_tc_ok]
      split <;> rfl

theorem bindings_erases (s : Statement) :
    (bindings s).1 = NFY_NBN_ValidatorSummary.chain (common s) (parts s) (NFY_NBN_ValidatorSummary.tail enc s) := by
  unfold bindings NFY_NBN_ValidatorSummary.chain
  repeat' first | split | rfl | exact tail_erases s

theorem erases (s : Statement) : (run s).1 =
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [← NFY_NED_CodecComposition.validator s]
  change (run s).1 = NFY_NBN_ValidatorSummary.run enc transfer withdrawal s
  unfold run NFY_NBN_ValidatorSummary.run
  split
  · rfl
  · split
    · rfl
    · unfold payment
      cases h : NFY_NBN_ValidatorSummary.paymentWith transfer withdrawal s with
      | fail e => simp only [h,bind_tc_fail]
      | div => simp only [h,bind_tc_div]
      | ok r =>
        cases r with
        | Err e => simp only [h,bind_tc_ok]
        | Ok bytes =>
          simp only [h,bind_tc_ok]
          exact bindings_erases s

/-- Every logged lane uses this statement's exact nullifier projection. -/
theorem lane_same (s : Statement) (d : Array U32 8#usize)
    (reached : Call.lane d ∈ (run s).2) : d = (parts s).2.2.2.2.1 := by
  unfold run at reached
  split at reached
  · cases reached
  · split at reached
    · cases reached
    · cases h : payment s with
      | fail e => simp only [h,List.mem_singleton] at reached; cases reached
      | div => simp only [h,List.mem_singleton] at reached; cases reached
      | ok r => cases r with
        | Err e => simp only [h,List.mem_singleton] at reached; cases reached
        | Ok bytes =>
          simp only [h,List.mem_cons] at reached
          rcases reached with bad | reached
          · cases bad
          · unfold bindings at reached
            repeat' first | split at reached | cases reached
            unfold tail at reached
            cases h : NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1 with
            | fail e => simpa only [h,List.mem_singleton,Call.lane.injEq] using reached
            | div => simpa only [h,List.mem_singleton,Call.lane.injEq] using reached
            | ok r => cases r with
              | Err e => simpa only [h,List.mem_singleton,Call.lane.injEq] using reached
              | Ok l =>
                simp only [h] at reached
                split at reached
                · simpa only [List.mem_singleton,Call.lane.injEq] using reached
                · simp only [List.mem_cons,List.not_mem_nil,Call.lane.injEq,reduceCtorEq,or_false] at reached
                  exact reached

#print axioms tail_erases
#print axioms bindings_erases
#print axioms erases
#print axioms lane_same
end NFY_NED_ValidatorTrace
-- END copied NED_ValidatorTrace
-- BEGIN copied NED_ValidatorCallDomains: evidence/slice-s-compose-20261029/NED_ValidatorCallDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_ValidatorCallDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_ValidatorTrace

def TailShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.lane (parts s).2.2.2.2.1] ∨
  xs = [.lane (parts s).2.2.2.2.1,.late (common s).lane_transition NFY_NBN_LateResult.zero]

def Shape (s : Statement) (xs : List Call) : Prop :=
  xs = [] ∨ xs = [.payment s] ∨
  xs = [.payment s,.lane (parts s).2.2.2.2.1] ∨
  xs = [.payment s,.lane (parts s).2.2.2.2.1,.late (common s).lane_transition NFY_NBN_LateResult.zero]

theorem tail_shape (s : Statement) : TailShape s (tail s).2 := by
  unfold tail
  dsimp only
  cases h : NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1 with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok r => cases r with
    | Err e => simp only [h]; exact Or.inl rfl
    | Ok l =>
      simp only [h]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem bindings_shape (s : Statement) :
    (bindings s).2 = [] ∨ TailShape s (bindings s).2 := by
  unfold bindings
  repeat' first | split | exact Or.inl rfl | exact Or.inr (tail_shape s)

theorem shape (s : Statement) : Shape s (run s).2 := by
  unfold run
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · cases h : NFY_NED_ValidatorTrace.payment s with
      | fail e => simp only [h]; exact Or.inr (Or.inl rfl)
      | div => simp only [h]; exact Or.inr (Or.inl rfl)
      | ok r => cases r with
        | Err e => simp only [h]; exact Or.inr (Or.inl rfl)
        | Ok bytes =>
          simp only [h]
          rcases bindings_shape s with none | one | two
          · rw [none]; exact Or.inr (Or.inl rfl)
          · rw [one]; exact Or.inr (Or.inr (Or.inl rfl))
          · rw [two]; exact Or.inr (Or.inr (Or.inr rfl))

/-- A logged late call has the SAME full record and fixed local output width.
The whole root need not accept: an error returned by that call is retained. -/
theorem late_domain (s : Statement) (arg : NFY_NBN_LateSummary.Statement) (out : Slice U8)
    (reached : Call.late arg out ∈ (run s).2) :
    arg = (common s).lane_transition ∧ out = NFY_NBN_LateResult.zero ∧ out.length = 1520 := by
  rcases shape s with none | one | two | three
  · simp only [none,List.not_mem_nil] at reached
  · simp only [one,List.mem_singleton,reduceCtorEq] at reached
  · simp only [two,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at reached
  · simp only [three,List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.late.injEq] at reached
    obtain ⟨rfl,rfl⟩ := reached
    refine ⟨rfl,rfl,?_⟩
    simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
    rfl

theorem payment_same (s : Statement) (arg : Statement)
    (reached : Call.payment arg ∈ (run s).2) : arg = s := by
  rcases shape s with none | one | two | three <;>
    simp_all only [List.mem_cons,List.not_mem_nil,
      reduceCtorEq,false_or,or_false,Call.payment.injEq]

#print axioms tail_shape
#print axioms bindings_shape
#print axioms shape
#print axioms late_domain
#print axioms payment_same
end NFY_NED_ValidatorCallDomains
-- END copied NED_ValidatorCallDomains

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))

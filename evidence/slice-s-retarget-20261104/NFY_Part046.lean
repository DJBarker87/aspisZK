import Lean
import NFY_Part045
import NFY_Part044
import NFY_Part028
import NBH_ArrayEq

-- BEGIN copied NED_RawLatePrepare: evidence/slice-s-compose-20261029/NED_RawLatePrepare.lean
set_option autoImplicit false
namespace NFY_NED_RawLatePrepare
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct.aspis_statement

def run {T : Type} (output : Slice U8) (k : Slice U8 → Result T) : Result T := do
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output { «end» := 8#usize }
      let s1 ← lift (Array.to_slice pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
      let output4 ← Slice.update output3 9#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 10#usize, «end» := 12#usize }
      let i2 ← lift (UScalar.cast .U16 pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES)
      let a ← lift (core.num.U16.to_le_bytes i2)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output5 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 12#usize, «end» := 16#usize }
      let i3 ← lift (UScalar.cast .U32 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)
      let a1 ← lift (core.num.U32.to_le_bytes i3)
      let s7 ← lift (Array.to_slice a1)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output6 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 16#usize, «end» := 20#usize }
      let i4 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
      let i5 ← lift (UScalar.cast .U32 i4)
      let a2 ← lift (core.num.U32.to_le_bytes i5)
      let s10 ← lift (Array.to_slice a2)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output7 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 20#usize, «end» := 24#usize }
      let i6 ← lift (UScalar.cast .U32 1520#usize)
      let a3 ← lift (core.num.U32.to_le_bytes i6)
      let s13 ← lift (Array.to_slice a3)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output8 := index_mut_back4 s14
      k output8

theorem source {T : Type} (out : Slice U8) (k : Slice U8 → Result T) :
    run out k = NFY_NBN_LatePrepare.run out k := by
  unfold run NFY_NBN_LatePrepare.run
  simp only [NFY_NED_LateEncodingConstants.magic,NFY_NED_LateEncodingConstants.version,
    NFY_NED_LateEncodingConstants.items,NFY_NED_LateEncodingConstants.header,
    NFY_NED_LateEncodingConstants.live_bytes,NFY_NED_LateEncodingConstants.after_bytes]

theorem exact {T : Type} (out : Slice U8) (size : out.length = 1520)
    (k : Slice U8 → Result T) : run out k = k (NFY_NBN_LatePrepare.value out) :=
  (source out k).trans (NFY_NBN_LatePrepare.exact out size k)

#print axioms source
#print axioms exact
end NFY_NED_RawLatePrepare
-- END copied NED_RawLatePrepare
-- BEGIN copied NED_RawLatePreflight: evidence/slice-s-compose-20261029/NED_RawLatePreflight.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawLatePreflight
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem option_ne (a b : Option U64) :
    core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) a b =
      ok (decide (a ≠ b)) := by
  cases a <;> cases b
  all_goals simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    core.option.Option.Insts.CoreCmpPartialEqOption,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEqU64,core.cmp.impls.PartialEqU64.eq,
    AspisR1AdapterReconstruct.optionDiscriminant_none,
    AspisR1AdapterReconstruct.optionDiscriminant_some]
  all_goals first | rfl | decide | scalar_tac

#print axioms option_ne
end NFY_NED_RawLatePreflight
-- END copied NED_RawLatePreflight
-- BEGIN copied NED_RawLateSource: evidence/slice-s-compose-20261029/NED_RawLateSource.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawLateSource
open Aeneas Aeneas.Std Result NFY_NED_LateCarriers
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1.pair_tree_profile

theorem factor (s : TLate) (out : Slice U8) (size : out.length = 1520)
    (index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
      some s.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 (toRawLate s) out =
      (do let filled ← core.slice.Slice.fill core.clone.CloneU8 out 0#u8
          NFY_NED_RawLatePrepare.run filled (NFY_NED_RawLateTail.run s)) := by
  have len : Slice.len out = 1520#usize := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    NFY_NED_LateEncodingConstants.size,bind_tc_ok,len,bne_self_eq_false,if_false,
    NFY_NED_LateCarrierFields.live,NFY_NED_LateCarrierFields.after,
    NFY_NED_LateCarrierFields.live_index,NFY_NED_LateCarrierFields.after_index,
    lift,NFY_NED_RawLatePreflight.option_ne,index,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true]
  have tail_eq : NFY_NED_RawLateFactor.raw s = NFY_NED_RawLateTail.run s :=
    funext (NFY_NED_RawLateFactor.raw_eq s)
  rw [← tail_eq]
  rfl

#print axioms factor
end NFY_NED_RawLateSource
-- END copied NED_RawLateSource
-- BEGIN copied NED_LateEncodingCohort: evidence/slice-s-compose-20261029/NED_LateEncodingCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_LateEncodingCohort
open Aeneas Aeneas.Std Result NFY_NED_LateCarriers NFY_NED_LateValidatorCohorts NFY_NED_ErrorCarriers
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1.pair_tree_profile

theorem result (s : TLate) (out : Slice U8) :
    encode_pool_v1_pair_late_public_statement_v1 (toRawLate s) out =
    NFY_NED_LiveEncodingCohort.mapStateOuter toRawPoolV1PairLatePublicStatementErrorV1
      (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s out) := by
  rw [NFY_NBN_LateResult.source]
  by_cases size : out.length = 1520
  · rw [if_neg (not_not.mpr size)]
    by_cases index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
        some s.candidate_afterstate.next_pair_index
    · rw [if_neg (not_not.mpr index),NFY_NED_RawLateSource.factor s out size index]
      have fill : core.slice.Slice.fill core.clone.CloneU8 out 0#u8 = ok NFY_NBN_LateResult.zero := by
        rw [NFY_NBK_Fill.source]
        congr 1
        apply Subtype.ext
        change List.replicate out.length 0#u8 = List.replicate 1520 0#u8
        rw [size]
      have zero_size : NFY_NBN_LateResult.zero.length = 1520 := by
        simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      rw [fill]
      simp only [bind_tc_ok]
      rw [NFY_NED_RawLatePrepare.exact NFY_NBN_LateResult.zero zero_size]
      change NFY_NED_RawLateTail.run s NFY_NBN_LateResult.header = _
      rw [NFY_NED_RawLateTail.exact s _ NFY_NBN_LateResult.header_length]
      rfl
    · rw [if_pos index]
      have len : Slice.len out = 1520#usize := by scalar_tac
      simp [encode_pool_v1_pair_late_public_statement_v1,NFY_NED_LateEncodingConstants.size,
        NFY_NED_LateCarrierFields.live,NFY_NED_LateCarrierFields.after,NFY_NED_LateCarrierFields.live_index,
        NFY_NED_LateCarrierFields.after_index,len,lift,NFY_NED_RawLatePreflight.option_ne,index,
        NFY_NED_LiveEncodingCohort.mapStateOuter,mapResult,toRawPoolV1PairLatePublicStatementErrorV1]
  · rw [if_pos size]
    have guard : (Slice.len out != 1520#usize) = true := by scalar_tac
    simp only [encode_pool_v1_pair_late_public_statement_v1,NFY_NED_LateEncodingConstants.size,
      bind_tc_ok,guard,if_true,NFY_NED_LiveEncodingCohort.mapStateOuter,mapResult,
      toRawPoolV1PairLatePublicStatementErrorV1]

#print axioms result
end NFY_NED_LateEncodingCohort
-- END copied NED_LateEncodingCohort
-- BEGIN copied NED_CommonEncodeCohort: evidence/slice-s-compose-20261029/NED_CommonEncodeCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_CommonEncodeCohort
open Aeneas Aeneas.Std Result NFY_NED_PaymentCohorts
abbrev TK := AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind
abbrev RK := AspisR1AdapterReconstruct.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind

def toRawKind : TK → RK
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

/-- SAME arbitrary output prestate, magic, kind and common fields; this is
symbolic equality between emitted bodies, not a concrete buffer evaluation. -/
theorem source (out : Array U8 216#usize) (magic : Array U8 4#usize) (kind : TK) (c : C) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
      out magic (toRawKind kind) (toRawCommon c) =
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common out magic kind c := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common
  simp only [
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.POOL_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.NULLIFIER_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ASSET_ID_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.NULLIFIER_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.ASSET_ID_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION]
  cases kind <;> rfl

theorem result (out : Array U8 216#usize) (magic : Array U8 4#usize) (kind : TK) (c : C) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
      out magic (toRawKind kind) (toRawCommon c) =
    ok (NFY_NBP_CommonBytes.encoded out magic kind c) := by
  rw [source,NFY_NBP_CommonBytes.result]

#print axioms source
#print axioms result
end NFY_NED_CommonEncodeCohort
-- END copied NED_CommonEncodeCohort
-- BEGIN copied NED_TransferEncodingCohort: evidence/slice-s-compose-20261029/NED_TransferEncodingCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_TransferEncodingCohort
open Aeneas Aeneas.Std Result NFY_NED_PaymentCohorts NFY_NED_CommonValidation
open AspisR1AdapterReconstruct

theorem result (p : T) :
    aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 (toRawTransfer p) =
    ok (mapPayment (NFY_NBP_PaymentModel.transfer_encoded p)) := by
  simp only [aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1,
    NFY_NED_PaymentValidation.transfer_result,bind_tc_ok]
  unfold NFY_NBP_PaymentModel.transfer_encoded
  cases h : NFY_NBG_PaymentValidators.transfer p with
  | Err e =>
    simp [h,mapPayment,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,mapPayment,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [NFY_NED_PaymentCohorts.transfer_common]
    simp only [bind_tc_ok]
    have encoded := NFY_NED_CommonEncodeCohort.result (Array.repeat 216#usize 0#u8)
      aspis_statement.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
      .PrivateTransfer (NFY_NBG_PaymentValidators.tc p)
    simp only [NFY_NED_CommonEncodeCohort.toRawKind] at encoded
    rw [encoded]
    simp only [bind_tc_ok,NFY_NED_DigestCohorts.digest_encode,NFY_NBP_DigestEncode.result,lift,
      aspis_statement.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      aspis_statement.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    simp only [toRawTransfer,AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1PrivateTransferPublicV1]
    unfold NFY_NBP_PaymentModel.transfer_bytes
    simp only [aspis_statement.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
      AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC]
    generalize common : NFY_NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
      (Array.make 4#usize [65#u8,83#u8,67#u8,80#u8])
      AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
      (NFY_NBG_PaymentValidators.tc p) = out
    rw [NFY_NBP_ArrayIndex.index_mut out 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice out 152#usize 184#usize) (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range out 152#usize 184#usize
      (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize first : out.setSlice! 152 (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).val = out1
    rw [NFY_NBP_ArrayIndex.suffix_index out1 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice out1 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range out1 184#usize 216#usize
      (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl

#print axioms result
end NFY_NED_TransferEncodingCohort
-- END copied NED_TransferEncodingCohort
-- BEGIN copied NED_WithdrawalEncodingCohort: evidence/slice-s-compose-20261029/NED_WithdrawalEncodingCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_WithdrawalEncodingCohort
open Aeneas Aeneas.Std Result NFY_NED_PaymentCohorts NFY_NED_CommonValidation
open AspisR1AdapterReconstruct

theorem result (p : W) :
    aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 (toRawWithdrawal p) =
    ok (mapPayment (NFY_NBP_PaymentModel.withdrawal_encoded p)) := by
  simp only [aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1,
    NFY_NED_PaymentValidation.withdrawal_result,bind_tc_ok]
  unfold NFY_NBP_PaymentModel.withdrawal_encoded
  cases h : NFY_NBG_PaymentValidators.withdrawal p with
  | Err e =>
    simp [h,mapPayment,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,mapPayment,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [NFY_NED_PaymentCohorts.withdrawal_common]
    simp only [bind_tc_ok]
    have encoded := NFY_NED_CommonEncodeCohort.result (Array.repeat 216#usize 0#u8)
      aspis_statement.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
      .Withdrawal (NFY_NBG_PaymentValidators.wc p)
    simp only [NFY_NED_CommonEncodeCohort.toRawKind] at encoded
    rw [encoded]
    simp only [bind_tc_ok,NFY_NED_DigestCohorts.digest_encode,NFY_NBP_DigestEncode.result,lift,
      aspis_statement.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      aspis_statement.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    simp only [toRawWithdrawal,AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1WithdrawalPublicV1]
    unfold NFY_NBP_PaymentModel.withdrawal_bytes
    simp only [aspis_statement.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
      AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC]
    generalize common : NFY_NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
      (Array.make 4#usize [65#u8,83#u8,87#u8,80#u8])
      AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal
      (NFY_NBG_PaymentValidators.wc p) = out
    rw [NFY_NBP_ArrayIndex.index_mut out 148#usize 152#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice out 148#usize 152#usize) (core.num.U32.to_le_bytes p.amount).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range out 148#usize 152#usize (core.num.U32.to_le_bytes p.amount) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize amount : out.setSlice! 148 (core.num.U32.to_le_bytes p.amount).val = out1
    rw [NFY_NBP_ArrayIndex.index_mut out1 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice out1 152#usize 184#usize) p.destination_token_account.to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range out1 152#usize 184#usize p.destination_token_account (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize destination : out1.setSlice! 152 p.destination_token_account.val = out2
    rw [NFY_NBP_ArrayIndex.suffix_index out2 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NFY_NBP_ArrayIndex.slice out2 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NFY_NBP_ArrayIndex.copy_range out2 184#usize 216#usize (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl

#print axioms result
end NFY_NED_WithdrawalEncodingCohort
-- END copied NED_WithdrawalEncodingCohort
-- BEGIN copied NED_ValidatorStatus: evidence/slice-s-compose-20261029/NED_ValidatorStatus.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_ValidatorStatus
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable

def payment (s : Statement) : core.result.Result (Array U8 216#usize) PaymentError :=
  match s with
  | .PrivateTransfer _ p => NFY_NBP_PaymentModel.transfer_encoded p
  | .Withdrawal _ p => NFY_NBP_PaymentModel.withdrawal_encoded p

def status (s : Statement) : core.result.Result Unit NFY_NBN_StatementResult.Error :=
  let c := common s
  if c.master_account = zero ∨ c.checkpoint_account = zero ∨ c.selected_lane_account = zero then .Err .NonZeroBinding
  else if 8 ≤ c.output_lane.val then .Err .InvalidOutputLane
  else match payment s with
    | .Err e => .Err (.Payment e)
    | .Ok _ => suffix s

theorem payment_source (s : Statement) : NFY_NBN_StatementResult.payment s = ok (payment s) := by
  cases s <;> simp only [NFY_NBN_StatementResult.payment,payment,NFY_NBP_TransferEncode.result,NFY_NBP_WithdrawalEncode.result]

theorem source (s : Statement) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (status s) := by
  rw [NFY_NBN_StatementResult.source]
  unfold NFY_NBN_StatementResult.result status
  rw [payment_source]
  dsimp (config := {zeta := true,zetaHave := true}) only
  simp only [bind_tc_ok]
  by_cases zero : (common s).master_account = NFY_NBN_StatementResult.zero ∨
      (common s).checkpoint_account = NFY_NBN_StatementResult.zero ∨
      (common s).selected_lane_account = NFY_NBN_StatementResult.zero
  · simp only [if_pos zero]
  · simp only [if_neg zero]
    by_cases lane : 8 ≤ (common s).output_lane.val
    · simp only [if_pos lane]
    · simp only [if_neg lane]
      cases h : payment s <;> rfl

#print axioms payment_source
#print axioms source
end NFY_NED_ValidatorStatus
-- END copied NED_ValidatorStatus
-- BEGIN copied NED_RawWordArrayEq: evidence/slice-s-compose-20261029/NED_RawWordArrayEq.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NED_RawWordArrayEq
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
attribute [local instance] Classical.propDecidable

theorem list_eq (xs ys : List U32) (hlen : xs.length = ys.length) :
    List.allM (fun (x,y) => do
      let b ← AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y
      ok (decide (¬ b = true))) (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM,pure]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      have tail : xs.length=ys.length := by simpa using hlen
      rw [List.zip_cons_cons]
      simp only [List.allM]
      have eqv : (do let b ← AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y; ok (decide (¬ b = true))) = ok (decide (x=y)) := by
        simp [AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
      rw [eqv]
      by_cases same : x=y
      · simp only [same,decide_true,bind_tc_ok,if_pos]
        simpa only [List.cons.injEq, true_and, liftFun2, bind_tc_ok] using ih ys tail
      · simp [same,pure]

theorem source {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.eq AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b = ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have length : a.length=b.length := by have := a.property; have := b.property; scalar_tac
  rw [if_pos length, list_eq a.val b.val (by have := a.property; have := b.property; scalar_tac)]
  have eqv : (a.val=b.val) ↔ a=b := by
    cases a
    cases b
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  simp only [eqv]

theorem ne {n : Usize} (a b : Array U32 n) :
    Aeneas.Std.core.array.equality.PartialEqArray.ne
      AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b =
      ok (decide (a ≠ b)) := by
  simp [Aeneas.Std.core.array.equality.PartialEqArray.ne,source]

#print axioms ne
#print axioms list_eq
#print axioms source
end NFY_NED_RawWordArrayEq
-- END copied NED_RawWordArrayEq
-- BEGIN copied NED_StatementCarrierFields: evidence/slice-s-compose-20261029/NED_StatementCarrierFields.lean
set_option autoImplicit false
namespace NFY_NED_StatementCarrierFields
open NFY_NED_ReconstructCarriers NFY_NED_PaymentCohorts NFY_NED_LateCarriers

theorem transfer (c : NFY_NED_ReconstructCarriers.Common) (p : T) :
    toRaw (.PrivateTransfer c p) =
    .PrivateTransfer (NFY_NED_ReconstructCarriers.toRawCommon c) (toRawTransfer p) := by rfl

theorem withdrawal (c : NFY_NED_ReconstructCarriers.Common) (p : W) :
    toRaw (.Withdrawal c p) =
    .Withdrawal (NFY_NED_ReconstructCarriers.toRawCommon c) (toRawWithdrawal p) := by rfl

theorem master (c : NFY_NED_ReconstructCarriers.Common) :
    (NFY_NED_ReconstructCarriers.toRawCommon c).master_account = c.master_account := by rfl
theorem checkpoint (c : NFY_NED_ReconstructCarriers.Common) :
    (NFY_NED_ReconstructCarriers.toRawCommon c).checkpoint_account = c.checkpoint_account := by rfl
theorem selected_lane (c : NFY_NED_ReconstructCarriers.Common) :
    (NFY_NED_ReconstructCarriers.toRawCommon c).selected_lane_account = c.selected_lane_account := by rfl
theorem lane (c : NFY_NED_ReconstructCarriers.Common) :
    (NFY_NED_ReconstructCarriers.toRawCommon c).output_lane = c.output_lane := by rfl
theorem sequence (c : NFY_NED_ReconstructCarriers.Common) :
    (NFY_NED_ReconstructCarriers.toRawCommon c).checkpoint_sequence = c.checkpoint_sequence := by rfl
theorem pool (s : TSnapshot) : (toRawSnapshot s).pool = s.pool := by rfl
theorem deployment (s : TSnapshot) : (toRawSnapshot s).deployment_domain = s.deployment_domain := by rfl

#print axioms transfer
#print axioms withdrawal
#print axioms master
#print axioms checkpoint
#print axioms selected_lane
#print axioms lane
#print axioms sequence
#print axioms pool
#print axioms deployment
end NFY_NED_StatementCarrierFields
-- END copied NED_StatementCarrierFields
-- BEGIN copied NED_OutputLaneCohort: evidence/slice-s-compose-20261029/NED_OutputLaneCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_OutputLaneCohort
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev TE := AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev RE := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1

def mapAccount {T : Type} : core.result.Result T TE → core.result.Result T RE
  | .Ok v => .Ok v
  | .Err e => .Err (NFY_NED_ErrorCarriers.toRawPoolV1PairForestAccountErrorV1 e)

theorem result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d =
    ok (mapAccount (NFY_NBN_OutputLane.result d)) := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
  rw [NFY_NED_ScannerCohorts.account_result]
  simp only [bind_tc_ok]
  by_cases good : NBD_DigestInduction.Canonical d
  · simp only [good,decide_true,if_true,NFY_NED_DigestCohorts.first_byte,
      NFY_NBN_OutputLane.first_source,bind_tc_ok,lift,NFY_NBN_OutputLane.result,mapAccount]
  · simp [good,NFY_NBN_OutputLane.result,mapAccount,NFY_NED_ErrorCarriers.toRawPoolV1PairForestAccountErrorV1]

#print axioms result
end NFY_NED_OutputLaneCohort
-- END copied NED_OutputLaneCohort
-- BEGIN copied NED_RawValidatorTail: evidence/slice-s-compose-20261029/NED_RawValidatorTail.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawValidatorTail
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult NFY_NED_ErrorCarriers
attribute [local instance] Classical.propDecidable
abbrev RE := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def run (s : Statement) : Result (core.result.Result Unit RE) := do
  let lane ← AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 (parts s).2.2.2.2.1
  match lane with
  | .Err e => ok (.Err (.Account e))
  | .Ok l =>
    if l ≠ (common s).output_lane then ok (.Err .OutputLaneMismatch)
    else do
      let (r,_) ← AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
        (NFY_NED_LateCarriers.toRawLate (common s).lane_transition) NFY_NBN_LateResult.zero
      match r with
      | .Err e => ok (.Err (.LaneTransition e))
      | .Ok _ => ok (.Ok ())

theorem result (s : Statement) : run s = ok
    (NFY_NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 (NFY_NBN_BindingChecks.tail s)) := by
  unfold run NFY_NBN_BindingChecks.tail
  rw [NFY_NED_OutputLaneCohort.result]
  cases lane : NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => rfl
  | Ok l =>
    simp only [NFY_NED_OutputLaneCohort.mapAccount,bind_tc_ok]
    by_cases mismatch : l = (common s).output_lane
    · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
      rw [NFY_NED_LateEncodingCohort.result,NFY_NBN_LateResult.source]
      have len : NFY_NBN_LateResult.zero.length = 1520 := by
        simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      rw [if_neg (not_not.mpr len)]
      unfold lateStatus
      by_cases index : U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 =
          some (common s).lane_transition.candidate_afterstate.next_pair_index
      · simp only [if_neg (not_not.mpr index),NFY_NED_LiveEncodingCohort.mapStateOuter,bind_tc_ok,Aeneas.Std.uncurry]
        cases NFY_NBN_LateTail.status (common s).lane_transition <;> rfl
      · simp [index,NFY_NED_LiveEncodingCohort.mapStateOuter,NFY_NED_LateValidatorCohorts.mapResult,
          toRawPoolV1PairForestTerminalFormatErrorV1,toRawPoolV1PairLatePublicStatementErrorV1]
    · simp [mismatch,NFY_NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1]

#print axioms result
end NFY_NED_RawValidatorTail
-- END copied NED_RawValidatorTail
-- BEGIN copied NED_RawValidatorControl: evidence/slice-s-compose-20261029/NED_RawValidatorControl.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawValidatorControl
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult
open AspisR1AdapterReconstruct
abbrev E := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def tail (s : Statement) : Result (core.result.Result Unit E) := do
  let common := NFY_NED_ReconstructCarriers.toRawCommon (NFY_NBN_StatementResult.common s)
  let nullifier := (parts s).2.2.2.2.1
  let r2 ←
    aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
      nullifier
  let r3 ←
    core.result.Result.map_err
      aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1
      r2 ()
  let cf1 ←
    core.result.Result.Insts.CoreOpsTry.branch r3
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if val != common.output_lane
    then
      ok (core.result.Result.Err
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch)
    else
      let late_bytes := Array.repeat 1520#usize 0#u8
      let (s, _) ← lift (Array.to_slice_mut late_bytes)
      let (r4, _) ←
        aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
          common.lane_transition s
      let r5 ←
        core.result.Result.map_err
          aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1
          r4 ()
      let cf2 ←
        core.result.Result.Insts.CoreOpsTry.branch r5
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok ())
      | core.ops.control_flow.ControlFlow.Break residual
        =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
          residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
      residual

theorem tail_factor (s : Statement) : tail s = NFY_NED_RawValidatorTail.run s := by
  unfold tail NFY_NED_RawValidatorTail.run
  simp only [NFY_NED_StatementCarrierFields.lane,NFY_NED_LateCarrierFields.common_late]
  apply NFY_NBN_LateFactor.bind_ext
  intro lane
  cases lane with
  | Err e => rfl
  | Ok val =>
    simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
    by_cases same : val = (common s).output_lane
    · simp only [same,bne_self_eq_false,if_false,ne_eq,not_true_eq_false,
        Array.to_slice_mut,lift,bind_tc_ok,Aeneas.Std.uncurry]
      apply NFY_NBN_LateFactor.bind_ext
      intro late
      rcases late with ⟨r,out⟩
      cases r <;> rfl
    · simp only [bne_iff_ne,ne_eq,same,not_false_eq_true,if_true]

#print axioms tail_factor
end NFY_NED_RawValidatorControl
-- END copied NED_RawValidatorControl
-- BEGIN copied NED_RawValidatorBindings: evidence/slice-s-compose-20261029/NED_RawValidatorBindings.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawValidatorBindings
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult NFY_NED_ErrorCarriers
open AspisR1AdapterReconstruct
attribute [local instance] Classical.propDecidable

def run (s : Statement) : Result (core.result.Result Unit NFY_NED_RawValidatorControl.E) := do
  let statement := NFY_NED_ReconstructCarriers.toRaw s
  let common := NFY_NED_ReconstructCarriers.toRawCommon (NFY_NBN_StatementResult.common s)
  let (pool, deployment, anchor_sequence, anchor, nullifier, _) ←
    aspis_statement.pool_v1.pair_forest_terminal.statement_public_common
      statement
  let b3 ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 pool
      common.master_account
  if b3
  then
    ok (core.result.Result.Err
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
  else
    let b4 ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        deployment
        common.lane_transition.live_snapshot.deployment_domain
    if b4
    then
      ok (core.result.Result.Err
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch)
    else
      let b5 ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          common.lane_transition.live_snapshot.pool
          common.master_account
      if b5
      then
        ok (core.result.Result.Err
          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch)
      else
        if anchor_sequence != common.checkpoint_sequence
        then
          ok (core.result.Result.Err
            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch)
        else
          let b6 ←
            core.array.equality.PartialEqArray.ne
              aspis_core.field.M31.Insts.CoreCmpPartialEqM31 anchor
              common.historical_global_anchor
          if b6
          then
            ok (core.result.Result.Err
              aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch)
          else
            NFY_NED_RawValidatorControl.tail s

def chain (s : Statement) (t : Result (core.result.Result Unit NFY_NED_RawValidatorControl.E)) :
    Result (core.result.Result Unit NFY_NED_RawValidatorControl.E) :=
  let c := common s
  let p := parts s
  if p.1 ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then ok (.Err .DeploymentBindingMismatch)
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.2.1 ≠ c.checkpoint_sequence then ok (.Err .CheckpointBindingMismatch)
  else if p.2.2.2.1 ≠ c.historical_global_anchor then ok (.Err .HistoricalAnchorMismatch)
  else t

theorem source_factor (s : Statement) : run s = chain s (NFY_NED_RawValidatorControl.tail s) := by
  unfold run
  dsimp (config := {zeta := true,zetaHave := true}) only
  rw [NFY_NED_ReconstructCarriers.parts_argument]
  simp only [bind_tc_ok,NFY_NBN_ArrayNe.bytes,NFY_NED_RawWordArrayEq.ne,
    NFY_NED_StatementCarrierFields.master,NFY_NED_LateCarrierFields.common_late,
    NFY_NED_LateCarrierFields.live,NFY_NED_StatementCarrierFields.pool,NFY_NED_StatementCarrierFields.deployment,
    NFY_NED_StatementCarrierFields.sequence,NFY_NED_LateCarrierFields.common_anchor]
  unfold chain
  simp only [bne_iff_ne,decide_eq_true_eq]
  rcases parts s with ⟨a,b,c,d,e,f⟩
  rfl

/-- Tail remains an arbitrary native computation here. This certificate is
only the five comparison controls, not a full validator bridge. -/
theorem tail_reached (s : Statement)
    (master : (parts s).1 = (common s).master_account)
    (deployment : (parts s).2.1 = (common s).lane_transition.live_snapshot.deployment_domain)
    (pool : (common s).lane_transition.live_snapshot.pool = (common s).master_account)
    (sequence : (parts s).2.2.1 = (common s).checkpoint_sequence)
    (anchor : (parts s).2.2.2.1 = (common s).historical_global_anchor) :
    run s = NFY_NED_RawValidatorControl.tail s := by
  rw [source_factor]
  simp only [chain,master,deployment,pool,sequence,anchor,ne_eq,not_true_eq_false,if_false]

#print axioms source_factor
#print axioms tail_reached
end NFY_NED_RawValidatorBindings
-- END copied NED_RawValidatorBindings
-- BEGIN copied NEE_ValidatorBindings: evidence/slice-s-compose2-20261029/NEE_ValidatorBindings.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEE_ValidatorBindings
open Aeneas Aeneas.Std Result NFY_NBN_StatementResult NFY_NED_ErrorCarriers
attribute [local instance] Classical.propDecidable

theorem chain_transport (s : Statement) (t : core.result.Result Unit NFY_NBN_StatementResult.Error) :
    NFY_NED_RawValidatorBindings.chain s
      (ok (NFY_NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 t)) =
    ok (NFY_NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1
      (NFY_NBN_BindingChecks.chain (common s) (parts s) t)) := by
  unfold NFY_NED_RawValidatorBindings.chain NFY_NBN_BindingChecks.chain
  dsimp (config := {zeta := true,zetaHave := true}) only
  repeat' first | split | rfl
  all_goals simp_all only [if_pos,if_neg]

theorem result (s : Statement) :
    NFY_NED_RawValidatorBindings.run s =
    ok (NFY_NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1
      (suffix s)) := by
  rw [NFY_NED_RawValidatorBindings.source_factor,NFY_NED_RawValidatorControl.tail_factor,
    NFY_NED_RawValidatorTail.result,chain_transport,← NFY_NBN_BindingChecks.factor]

#print axioms chain_transport
#print axioms result
end NFY_NEE_ValidatorBindings
-- END copied NEE_ValidatorBindings

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))

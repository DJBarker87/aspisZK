import NBP_PaymentModel
set_option autoImplicit false
noncomputable section
namespace NBP_WithdrawalDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_PaymentModel

theorem fixed (b : Array U8 216#usize) :
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 b.to_slice = ok (withdrawal_decoded b) := by
  have eq32 : ∀ h, Usize.ofNatCore 32 h = 32#usize := fun _ => rfl
  have eq216 : ∀ h, Usize.ofNatCore 216 h = 216#usize := fun _ => rfl
  have tail32 : (b.val.drop 184).take 32 = b.val.drop 184 := by
    apply List.take_of_length_le
    simp [b.property]
  simp [eq32,eq216,tail32,Slice.drop,pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1,
    NBG_Header.header_result,NBP_CommonDecode.result,NBG_PaymentValidators.withdrawal_result,
    pool_v1.payment_relation.ASSET_ID_OFFSET,pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,Slice.length,Slice.len,b.property,
    core.array.TryFromArrayCopySlice.try_from,core.array.TryFromSharedArraySlice.try_from,
    atomic_statement.unwrap_fixed_slice,aspis_core.field.P,
    NBP_DigestDecode.result,NBG_PaymentChecks.common_result,
    withdrawal_decoded,withdrawal_public,NBP_Read.chunk,lift,bind_tc_ok,List.slice,
    pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
    pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    pool_v1.payment_relation.POOL_V1_CANONICAL_FEE,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,NBG_Header.slice_equal,
    core.result.Result.map_err,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  repeat' split
  all_goals simp_all

/-- All slice lengths, including rejection before any fixed-width read. -/
theorem result (bytes : Slice U8) :
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes =
      if h : bytes.val.length=216 then ok (withdrawal_decoded (⟨bytes.val,h⟩ : Array U8 216#usize))
      else ok (.Err .WrongLength) := by
  by_cases h : bytes.val.length=216
  · rw [dif_pos h]
    change pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 (Array.to_slice (⟨bytes.val,h⟩ : Array U8 216#usize)) = _
    exact fixed _
  · rw [dif_neg h]
    simp [pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1,core.array.TryFromSharedArraySlice.try_from,
      Slice.len,Slice.length,h,core.result.Result.map_err,
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
#print axioms result
#print axioms fixed
end NBP_WithdrawalDecode

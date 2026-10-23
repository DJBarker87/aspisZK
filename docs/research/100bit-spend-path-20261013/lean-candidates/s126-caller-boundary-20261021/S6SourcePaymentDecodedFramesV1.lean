import S6SourcePaymentDecodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentDecode
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

@[step] theorem transfer_validation_graph (public1 : PoolV1PrivateTransferPublicV1) :
    validate_pool_v1_private_transfer_public_v1 public1 ⦃ result => validate_pool_v1_private_transfer_public_v1 public1=ok result ⦄ := by
  obtain ⟨result,h⟩ := PaymentTotal.transfer_total public1
  apply exists_imp_spec
  exact ⟨result,h,h⟩

@[step] theorem withdrawal_validation_graph (public1 : PoolV1WithdrawalPublicV1) :
    validate_pool_v1_withdrawal_public_v1 public1 ⦃ result => validate_pool_v1_withdrawal_public_v1 public1=ok result ⦄ := by
  obtain ⟨result,h⟩ := PaymentTotal.withdrawal_total public1
  apply exists_imp_spec
  exact ⟨result,h,h⟩

def transfer_frame (bytes : Slice U8) (public1 : PoolV1PrivateTransferPublicV1) : Prop :=
  ∃ raw : Array U8 216#usize, raw.val=bytes.val ∧
    header_frame raw POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer ∧
    (∃ common, transfer_common public1=ok common ∧ common_frame raw common) ∧
    List.slice 148 152 raw.val=(core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val ∧
    (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical public1.recipient_commitment=ok encoded ∧
      encoded.val=List.slice 152 184 raw.val) ∧
    (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical public1.change_commitment=ok encoded ∧
      encoded.val=List.drop 184 raw.val) ∧
    validate_pool_v1_private_transfer_public_v1 public1=ok (core.result.Result.Ok ())

def withdrawal_frame (bytes : Slice U8) (public1 : PoolV1WithdrawalPublicV1) : Prop :=
  ∃ raw : Array U8 216#usize, raw.val=bytes.val ∧
    header_frame raw POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal ∧
    (∃ common, withdrawal_common public1=ok common ∧ common_frame raw common) ∧
    (core.num.U32.to_le_bytes public1.amount).val=List.slice 148 152 raw.val ∧
    public1.destination_token_account.val=List.slice 152 184 raw.val ∧
    (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical public1.change_commitment=ok encoded ∧
      encoded.val=List.drop 184 raw.val) ∧
    validate_pool_v1_withdrawal_public_v1 public1=ok (core.result.Result.Ok ())

/-- Complete accepted transfer field provenance derived from the actual decoder. -/
@[step] theorem transfer_frames (bytes : Slice U8) :
    decode_pool_v1_private_transfer_public_v1 bytes
      ⦃ result => ∀ public1, result=core.result.Result.Ok public1 → transfer_frame bytes public1 ⦄ := by
  unfold decode_pool_v1_private_transfer_public_v1
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r7 <;> simp_all)
  all_goals step*
  all_goals (intro public1 hp; cases hp)
  all_goals (unfold transfer_frame; refine ⟨val,?_,?_,?_,?_,?_,?_,?_⟩)
  all_goals (simp_all [transfer_common,List.slice])
  all_goals (
    have hm : List.take 4 (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val=
        (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val := by
      have h := (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).property
      have ht : List.take (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val.length
          (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val=
          (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val := List.take_length
      simpa [h] using ht
    exact s_post1.symm.trans hm)


/-- Complete accepted withdrawal field provenance derived from the actual decoder. -/
@[step] theorem withdrawal_frames (bytes : Slice U8) :
    decode_pool_v1_withdrawal_public_v1 bytes
      ⦃ result => ∀ public1, result=core.result.Result.Ok public1 → withdrawal_frame bytes public1 ⦄ := by
  unfold decode_pool_v1_withdrawal_public_v1
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r5 <;> simp_all)
  all_goals step*
  all_goals (cases r6 <;> simp_all)
  all_goals step*
  all_goals (intro public1 hp; cases hp)
  all_goals (unfold withdrawal_frame; refine ⟨val,?_,?_,?_,?_,?_,?_,?_⟩)
  all_goals (simp_all [withdrawal_common,List.slice,AspisS6ByteInverse.u32_to_from])

#print axioms transfer_frames
#print axioms withdrawal_frames
end AspisS6SourceCodec.PaymentDecode

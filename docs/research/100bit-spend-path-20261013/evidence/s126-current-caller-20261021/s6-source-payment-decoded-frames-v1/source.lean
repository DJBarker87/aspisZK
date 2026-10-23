import S6SourcePaymentDecodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentDecode
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

def transfer_frame (bytes : Slice U8) (public : PoolV1PrivateTransferPublicV1) : Prop :=
  ∃ raw : Array U8 216#usize, raw.val=bytes.val ∧
    header_frame raw POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer ∧
    (∃ common, transfer_common public=ok common ∧ common_frame raw common) ∧
    List.slice 148 152 raw.val=(core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val ∧
    (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical public.recipient_commitment=ok encoded ∧
      encoded.val=List.slice 152 184 raw.val) ∧
    (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical public.change_commitment=ok encoded ∧
      encoded.val=List.drop 184 raw.val)

def withdrawal_frame (bytes : Slice U8) (public : PoolV1WithdrawalPublicV1) : Prop :=
  ∃ raw : Array U8 216#usize, raw.val=bytes.val ∧
    header_frame raw POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal ∧
    (∃ common, withdrawal_common public=ok common ∧ common_frame raw common) ∧
    (core.num.U32.to_le_bytes public.amount).val=List.slice 148 152 raw.val ∧
    public.destination_token_account.val=List.slice 152 184 raw.val ∧
    (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical public.change_commitment=ok encoded ∧
      encoded.val=List.drop 184 raw.val)

/-- Complete accepted transfer field provenance derived from the actual decoder. -/
@[step] theorem transfer_frames (bytes : Slice U8) :
    decode_pool_v1_private_transfer_public_v1 bytes
      ⦃ result => ∀ public, result=core.result.Result.Ok public → transfer_frame bytes public ⦄ := by
  unfold decode_pool_v1_private_transfer_public_v1
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r7 <;> simp_all)
  all_goals step*
  all_goals (intro public hp; cases hp)
  all_goals (unfold transfer_frame; refine ⟨val,?_,?_,?_,?_,?_,?_⟩)
  all_goals (simp_all [transfer_common,List.slice])

/-- Complete accepted withdrawal field provenance derived from the actual decoder. -/
@[step] theorem withdrawal_frames (bytes : Slice U8) :
    decode_pool_v1_withdrawal_public_v1 bytes
      ⦃ result => ∀ public, result=core.result.Result.Ok public → withdrawal_frame bytes public ⦄ := by
  unfold decode_pool_v1_withdrawal_public_v1
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r5 <;> simp_all)
  all_goals step*
  all_goals (cases r6 <;> simp_all)
  all_goals step*
  all_goals (intro public hp; cases hp)
  all_goals (unfold withdrawal_frame; refine ⟨val,?_,?_,?_,?_,?_,?_⟩)
  all_goals (simp_all [withdrawal_common,List.slice,AspisS6ByteInverse.u32_to_from])

#print axioms transfer_frames
#print axioms withdrawal_frames
end AspisS6SourceCodec.PaymentDecode

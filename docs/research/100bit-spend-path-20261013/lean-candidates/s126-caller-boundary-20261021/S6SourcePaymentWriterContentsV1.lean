import S6PaymentFrameRecomposeV1
import S6PaymentCommonOutputV1
import S6PaymentTailChunkFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentContents
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

private theorem array_length {T : Type} {N : Usize} (a : Array T N) :
    a.val.length=N.val := a.property
private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

theorem common_prefix_length (magic : Array U8 4#usize)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) : (common_prefix magic kind common).length=148 := by
  simp [common_prefix,array_length,digest_chunks_length]

@[step] theorem u32_write_spec (value : U32) :
    lift (core.num.U32.to_le_bytes value)
      ⦃ result => result=core.num.U32.to_le_bytes value ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

def transfer_bytes (common : CommonPublicV1) (public1 : PoolV1PrivateTransferPublicV1) : List U8 :=
  common_prefix POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer common++
  List.replicate 4 0#u8++DigestContents.chunks public1.recipient_commitment++
  DigestContents.chunks public1.change_commitment

def withdrawal_bytes (common : CommonPublicV1) (public1 : PoolV1WithdrawalPublicV1) : List U8 :=
  common_prefix POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
    aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal common++
  (core.num.U32.to_le_bytes public1.amount).val++public1.destination_token_account.val++
  DigestContents.chunks public1.change_commitment

/-- Exact positive encoder graph. The binding and validation premises are
removed by the enclosing accepted-decode inverse, not assumed by its caller. -/
theorem transfer_write (public1 : PoolV1PrivateTransferPublicV1) (common : CommonPublicV1)
    (binding : transfer_common public1=ok common)
    (valid : validate_pool_v1_private_transfer_public_v1 public1=ok (core.result.Result.Ok ())) :
    encode_pool_v1_private_transfer_public_v1 public1
      ⦃ result => ∃ output, result=core.result.Result.Ok output ∧ output.val=transfer_bytes common public1 ⦄ := by
  obtain ⟨base,hbase,hbasezero⟩ := common_output
    (Array.repeat 216#usize 0#u8) POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer common
  have hbasebytes := hbasezero rfl
  obtain ⟨recipient,hrecipient,hrecipientbytes⟩ := spec_imp_exists
    (DigestContents.encode_contents public1.recipient_commitment)
  obtain ⟨change,hchange,hchangebytes⟩ := spec_imp_exists
    (DigestContents.encode_contents public1.change_commitment)
  unfold encode_pool_v1_private_transfer_public_v1
  rw [valid,binding]
  unfold core.result.Result.Insts.CoreOpsTry.branch
  simp only [bind_tc_ok]
  rw [hbase,hrecipient,hchange]
  simp only [bind_tc_ok]
  unfold FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals refine ⟨_,rfl,?_⟩
  all_goals (simp_all only [array_slice_length] <;> try scalar_tac)
  all_goals simp_all only [Array.to_slice]
  unfold transfer_bytes
  exact AspisS6SliceFrame.payment_transfer_tail 0#u8 _ _ _
    (common_prefix_length _ _ _) (digest_chunks_length _) (digest_chunks_length _)

theorem withdrawal_write (public1 : PoolV1WithdrawalPublicV1) (common : CommonPublicV1)
    (binding : withdrawal_common public1=ok common)
    (valid : validate_pool_v1_withdrawal_public_v1 public1=ok (core.result.Result.Ok ())) :
    encode_pool_v1_withdrawal_public_v1 public1
      ⦃ result => ∃ output, result=core.result.Result.Ok output ∧ output.val=withdrawal_bytes common public1 ⦄ := by
  obtain ⟨base,hbase,hbasezero⟩ := common_output
    (Array.repeat 216#usize 0#u8) POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal common
  have hbasebytes := hbasezero rfl
  obtain ⟨change,hchange,hchangebytes⟩ := spec_imp_exists
    (DigestContents.encode_contents public1.change_commitment)
  unfold encode_pool_v1_withdrawal_public_v1
  rw [valid,binding]
  unfold core.result.Result.Insts.CoreOpsTry.branch
  simp only [bind_tc_ok]
  rw [hbase,hchange]
  simp only [bind_tc_ok]
  unfold AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals refine ⟨_,rfl,?_⟩
  all_goals (simp_all only [array_slice_length] <;> try scalar_tac)
  all_goals simp_all only [Array.to_slice]
  unfold withdrawal_bytes
  exact AspisS6SliceFrame.payment_withdrawal_tail 0#u8 _ _ _ _
    (common_prefix_length _ _ _) (by simp [array_length])
    (by simp [array_length]) (digest_chunks_length _)

#print axioms common_prefix_length
#print axioms transfer_write
#print axioms withdrawal_write
end AspisS6SourceCodec.PaymentContents

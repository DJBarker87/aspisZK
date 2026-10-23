import S6SourcePaymentDecodeHelpersV1
import S6ByteInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentDecode
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

@[step] theorem u32_read_spec (bytes : Array U8 4#usize) :
    lift (core.num.U32.from_le_bytes bytes)
      ⦃ result => result=core.num.U32.from_le_bytes bytes ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

@[step] theorem u64_read_spec (bytes : Array U8 8#usize) :
    lift (core.num.U64.from_le_bytes bytes)
      ⦃ result => result=core.num.U64.from_le_bytes bytes ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

def common_frame (bytes : Array U8 216#usize) (common : CommonPublicV1) : Prop :=
  common.pool.val=List.slice 8 40 bytes.val ∧
  common.deployment_domain.val=List.slice 40 72 bytes.val ∧
  (core.num.U64.to_le_bytes common.anchor_sequence).val=List.slice 72 80 bytes.val ∧
  (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical common.anchor_root=ok encoded ∧
    encoded.val=List.slice 80 112 bytes.val) ∧
  (∃ encoded, aspis_statement.atomic_statement.encode_digest_canonical common.nullifier=ok encoded ∧
    encoded.val=List.slice 112 144 bytes.val) ∧
  (core.num.U32.to_le_bytes common.asset_id).val=List.slice 144 148 bytes.val

/-- TOTAL common decoder with exact accepted byte frames for every field.
Digest frame witnesses are the actual concrete encoder returns. -/
@[step] theorem common_spec (bytes : Array U8 216#usize) :
    decode_common bytes ⦃ result => ∀ common,
      result=core.result.Result.Ok common → common_frame bytes common ⦄ := by
  unfold decode_common ASSET_ID_OFFSET AMOUNT_OR_RESERVED_OFFSET POOL_OFFSET
    DEPLOYMENT_DOMAIN_OFFSET ANCHOR_SEQUENCE_OFFSET ANCHOR_ROOT_OFFSET NULLIFIER_OFFSET
  step*
  all_goals (cases r <;> simp_all)
  all_goals step*
  all_goals (cases r1 <;> simp_all)
  all_goals step*
  all_goals (cases r2 <;> simp_all)
  all_goals step*
  all_goals (cases r3 <;> simp_all)
  all_goals step*
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r7 <;> simp_all)
  all_goals step*
  all_goals (intro common hc; cases hc)
  all_goals (simp_all [common_frame,AspisS6ByteInverse.u32_to_from,
    AspisS6ByteInverse.u64_to_from])

theorem common_total (bytes : Array U8 216#usize) :
    ∃ result, decode_common bytes=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (common_spec bytes)
  exact ⟨result,h⟩

#print axioms common_spec
#print axioms common_total
end AspisS6SourceCodec.PaymentDecode

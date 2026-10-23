import S6SourcePaymentDecodedFramesV1
import S6PaymentCommonChunkFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentContents
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

private theorem array_length {T : Type} {N : Usize} (a : Array T N) :
    a.val.length=N.val := a.property

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

theorem digest_chunks_length (digest : Array U32 8#usize) :
    (DigestContents.chunks digest).length=32 := by
  simp [DigestContents.chunks,array_length]

@[step] theorem u64_write_spec (value : U64) :
    lift (core.num.U64.to_le_bytes value)
      ⦃ result => result=core.num.U64.to_le_bytes value ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

private theorem byte_cast_identity (value : U8) :
    UScalar.cast .U8 value=value := by scalar_tac

def common_prefix (magic : Array U8 4#usize)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) : List U8 :=
  magic.val++[1#u8,(read_discriminant kind : U8),1#u8,0#u8]++
    common.pool.val++common.deployment_domain.val++
    (core.num.U64.to_le_bytes common.anchor_sequence).val++
    DigestContents.chunks common.anchor_root++DigestContents.chunks common.nullifier++
    (core.num.U32.to_le_bytes common.asset_id).val

/-- Exact bytes produced by the actual common writer on its actual enclosing
payment caller's initialized buffer. All native fields and all writes retained. -/
@[step] theorem common_contents (magic : Array U8 4#usize)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) :
    encode_common (Array.repeat 216#usize 0#u8) magic kind common
      ⦃ output => output.val=common_prefix magic kind common++List.replicate 68 0#u8 ⦄ := by
  unfold encode_common POOL_OFFSET DEPLOYMENT_DOMAIN_OFFSET ANCHOR_SEQUENCE_OFFSET
    ANCHOR_ROOT_OFFSET NULLIFIER_OFFSET ASSET_ID_OFFSET AMOUNT_OR_RESERVED_OFFSET
    POOL_V1_PAYMENT_STATEMENT_VERSION
    aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  simp only [aspis_core.field.M31.to_le_bytes,bind_tc_ok]
  step*
  all_goals (simp_all only [array_slice_length] <;> try scalar_tac)
  all_goals (simp_all only [Array.to_slice,Aeneas.Std.Array.set,byte_cast_identity])
  all_goals simp_all [Array.repeat]
  unfold common_prefix
  rw [AspisS6SliceFrame.payment_header_writes magic.val (by simpa using magic.property)
    0#u8 1#u8 (read_discriminant kind) 1#u8]
  apply AspisS6SliceFrame.payment_common_chunks
  all_goals simp [array_length,digest_chunks_length]

#print axioms digest_chunks_length
#print axioms common_contents
end AspisS6SourceCodec.PaymentContents

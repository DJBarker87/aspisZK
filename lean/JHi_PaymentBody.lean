import JHi_PaymentValidation
import JHi_RetypeSuccess
import JFs_PublicEncoders
set_option autoImplicit false
namespace AspisR1.JHi_PaymentBody
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
/-- The actual encoder continuation after successful payment validation. -/
def body : Result (Array U8 216#usize) := do
  let output := Array.repeat 216#usize 0#u8
  let cpv ←
    aspis_statement.pool_v1.payment_relation.transfer_common JHg_RawPrefix.payment
  let output1 ←
    aspis_statement.pool_v1.payment_relation.encode_common output
      aspis_statement.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
      aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
      cpv
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output1
      {
        start :=
          aspis_statement.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
        «end» :=
          aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
      }
  let a ←
    aspis_statement.atomic_statement.encode_digest_canonical
      JHg_RawPrefix.payment.recipient_commitment
  let s1 ← lift (Array.to_slice a)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output2
      {
        start :=
          aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
      }
  let a1 ←
    aspis_statement.atomic_statement.encode_digest_canonical
      JHg_RawPrefix.payment.change_commitment
  let s4 ← lift (Array.to_slice a1)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output3 := index_mut_back1 s5
  ok output3

theorem raw :
    aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 JHg_RawPrefix.payment =
    (body >>= fun x=>ok (core.result.Result.Ok x : core.result.Result _
      aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) := by
  unfold aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
  rw [JHi_PaymentValidation.source]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  congr 1
#print axioms raw
end AspisR1.JHi_PaymentBody

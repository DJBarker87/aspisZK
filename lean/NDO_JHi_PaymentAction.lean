import NDO_JHi_CommonEncoder
import JHi_RetypeSuccess
set_option autoImplicit false
namespace AspisR1.JHi_PaymentAction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

def raw (p : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,
    p.recipient_commitment,p.change_commitment⟩

def body (p : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : Result (Array U8 216#usize) := do
  let output := Array.repeat 216#usize 0#u8
  let cpv ←
    AspisR1TerminalDecoder.pool_v1.payment_relation.transfer_common p
  let output1 ←
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common output
      AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
      AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
      cpv
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output1
      {
        start :=
          AspisR1TerminalDecoder.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
        «end» :=
          AspisR1TerminalDecoder.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
      }
  let a ←
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
      p.recipient_commitment
  let s1 ← lift (Array.to_slice a)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output2
      {
        start :=
          AspisR1TerminalDecoder.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
      }
  let a1 ←
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
      p.change_commitment
  let s4 ← lift (Array.to_slice a1)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output3 := index_mut_back1 s5
  ok output3

end AspisR1.JHi_PaymentAction

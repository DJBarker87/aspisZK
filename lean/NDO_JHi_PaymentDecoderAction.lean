import NDO_JHi_PaymentAction
set_option autoImplicit false
namespace AspisR1.JHi_PaymentDecoderAction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct JHi_PaymentAction

theorem source (p : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (validated : AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 p=ok (.Ok ())) :
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p=
    (body p >>= fun x=>ok (core.result.Result.Ok x : core.result.Result _
      AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) := by
  unfold AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,AspisR1TerminalDecoder.pool_v1.payment_relation.transfer_common,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  congr 1
#print axioms source
end AspisR1.JHi_PaymentDecoderAction

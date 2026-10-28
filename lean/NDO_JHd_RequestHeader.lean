import JHd_RequestFuns
import NDO_JFs_PaymentHeader
set_option autoImplicit false
namespace AspisR1.JHd_RequestHeader
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.payment_relation
open JFs_PaymentHeader
theorem source : require_header JFs_PaymentArray.value POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer=ok (.Ok ()) := by
  unfold require_header
  simp only [magic_call,b4,b5,b6,b7,bind_tc_ok]
  unfold POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC POOL_V1_PAYMENT_STATEMENT_VERSION
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  rfl

#print axioms source
end AspisR1.JHd_RequestHeader

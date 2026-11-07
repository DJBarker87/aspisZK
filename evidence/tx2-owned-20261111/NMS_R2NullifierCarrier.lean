import NMS_RequestModels
import NMS_R2N_Interpreted
set_option autoImplicit false
namespace NMS_R2NullifierCarrier
open Aeneas Aeneas.Std Result
open AspisR20Request.pool_v1.pair_forest_terminal
/-- Every word survives the R20 request/payment conversion into the actual
adapter nullifier getter. This is a full array equation, not a projection. -/
def nullifier (p : PoolV1PairForestTerminalPaymentV1) : Array U32 8#usize :=
 match p with | .PrivateTransfer p => p.nullifier | .Withdrawal p => p.nullifier

theorem payment (p : PoolV1PairForestTerminalPaymentV1) :
 NMS_RequestModels.nullifier (AspisR1.NFY_JHd_RequestCarrier.payment p) = ok (nullifier p) := by
 cases p <;> rfl

theorem request (q : PoolV1PairForestTerminalRequestV1) :
 NMS_RequestModels.nullifier (AspisR1.NFY_JHd_RequestCarrier.request q).«public» =
 ok (nullifier q.«public») := payment q.«public»

theorem full (q : PoolV1PairForestTerminalRequestV1) :
 NMS_R2N_Interpreted.liftResult
  (NMS_RequestModels.nullifier (AspisR1.NFY_JHd_RequestCarrier.request q).«public») =
 RSL.Spec.pure (nullifier q.«public») := by
 rw [request]
 rfl
#print axioms payment
#print axioms request
#print axioms full
end NMS_R2NullifierCarrier

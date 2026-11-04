"""Extract the adopted request continuation text; children are explicit parameters."""
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent.parent
s=(R/'lean/JHd_RequestFuns.lean').read_text();key='def\n  pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1\n';start=s.index(key);end=s.index('\n/--',start);body=s[start:end]
body=body.replace(key,'def run\n  (transfer : Slice U8 → Result (core.result.Result pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError))\n  (withdrawal : Slice U8 → Result (core.result.Result pool_v1.payment_relation.PoolV1WithdrawalPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError))\n')
body=body.replace('pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1','transfer').replace('pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1','withdrawal')
text='''import JHd_RequestNative
import NED_RequestReadWindows
set_option autoImplicit false
noncomputable section
namespace NFD_RequestOracle
open Aeneas Aeneas.Std Result AspisR20Request
'''+body+'''
/-- MODEL continuation part of ruling(y). The native certificate must separately
establish the exact same320-byte input and216-byte payment window. -/
theorem array_result_state_effects {State : Type} (bytes : Array U8 320#usize) (state : State) :
    (run pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes,state,[]) := by rfl

/-- The installed wrapper keeps every error constructor and the same parsed
request; no accepted fixture is assumed. -/
def runSlice (bytes : Slice U8) : Result (core.result.Result AspisR1.JHd_RequestNative.Request AspisR1.JHd_RequestNative.FormatError) := do
  let array ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
  match array with
  | .Err _ => ok (.Err AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  | .Ok array =>
    let result ← run pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 array
    match result with
    | .Err error => ok (.Err (AspisR1.JHd_RequestCarrier.mapPoolV1PairForestTerminalFormatErrorV1 error))
    | .Ok request => ok (.Ok (AspisR1.JHd_RequestCarrier.request request))

theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (runSlice bytes,state,([] : List Unit)) =
    (AspisR1.JHd_RequestNative.decode bytes,state,[]) := by rfl

#print axioms array_result_state_effects
#print axioms result_state_effects
end NFD_RequestOracle
'''
(E/'NFD_RequestOracle.lean').write_text(text)

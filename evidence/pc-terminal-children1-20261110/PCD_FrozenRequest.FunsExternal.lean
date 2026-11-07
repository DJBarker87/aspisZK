import PCD_RequestCarrier
set_option autoImplicit false
noncomputable section
namespace PCD_FrozenRequest
open Aeneas Aeneas.Std
/-- Concrete standard Result combinator; both arms and the closure Result
are retained. The installed closure is the extracted constant InvalidInstructionData.
The native wrapper executes the original Rust combinator. -/
def core.result.Result.map_err {T E F O : Type}
    (ops : core.ops.function.FnOnce O E F) (value : core.result.Result T E)
    (environment : O) : Result (core.result.Result T F) := do
  match value with
  | .Ok result => .ok (.Ok result)
  | .Err error =>
    let error ← ops.call_once environment error
    .ok (.Err error)

/-- CLOSED NLO decoder substituted at the SAME slice. Structural maps preserve
all payment fields and all 22 terminal/nested error constructors. -/
def aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_v1
    (bytes : Slice U8) : Result (core.result.Result LocalRequest
      aspis_statement.pool_v1.pair_forest_terminal.PCD_PoolV1PairForestTerminalFormatErrorV1) := do
  let result ← NFY_NFD_RequestOracle.runSlice bytes
  match result with
  | .Ok request => .ok (.Ok (mapRequest request))
  | .Err error => .ok (.Err (mapPoolV1PairForestTerminalFormatErrorV1 error))
end PCD_FrozenRequest

import NFY_Part060
set_option autoImplicit false
namespace NMS_RequestModels
open Aeneas Aeneas.Std Result AdapterRw
/-- Fixed scalar getter on the exact emitted payment carrier; no model Ops. -/
def nullifier (p : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1) : Result (Array U32 8#usize) :=
 match p with
 | .PrivateTransfer p => ok p.nullifier
 | .Withdrawal p => ok p.nullifier
/-- The native decoder on the coherent CLOSED156 carrier, with the original
adapter error conversion. Child-root installation is a separate obligation. -/
def outputLane (digest : Array U32 8#usize) : Result
 (core.result.Result U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) := do
 let result ← AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 digest
 match result with
 | .Err _ => ok (.Err .NonCanonicalDigest)
 | .Ok lane => ok (.Ok lane)
end NMS_RequestModels

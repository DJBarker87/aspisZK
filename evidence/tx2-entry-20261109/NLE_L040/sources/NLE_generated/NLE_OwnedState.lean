import AdapterRwModel
import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NLE_Owned
open Aeneas Aeneas.Std Result AdapterRw
abbrev Account := r1_pool_adapter.owned.OwnedAccount
abbrev PE := solana_program_error.ProgramError
abbrev Validated := r1_pool_adapter.ValidatedAsqa
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev PR := core.result.Result Unit PE
structure Frame where
 program : solana_pubkey.Pubkey
 accounts : Slice Account
 data : Slice U8
 slot : core.result.Result U64 PE
structure State where
 frame : Frame
 validated : Option Validated := none
 proofBytes : Option (Slice U8) := none
 checkpoint : Option (Slice U8) := none
 proofEnd : Option Usize := none
 publicBytes : Option (Array U8 1880#usize) := none
inductive Event where
 | validate (state : State) (reply : Result (core.result.Result Validated PE))
 | proof (state : State) (account : Account) (reply : Result (core.result.Result (Slice U8) PE))
 | checkpoint (state : State) (account : Account) (reply : Result (core.result.Result (Slice U8) PE))
 | encode (state : State) (statement : Statement) (reply : Result (core.result.Result (Array U8 1880#usize) aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
 | tx2 (state : State) (publicBytes proof checkpoint : Slice U8) (reply : Result (core.result.Result Unit aspis_r1_cost_probe.verifier.Error))
 | error (state : State) (error : aspis_r1_cost_probe.verifier.Error) (reply : Result PE)
 | emit (state : State) (statement : Statement) (reply : Result PR)
abbrev Run (A : Type) := NJU_Log.Run Event A
/-- Error conversion is itself an entered child with a retained abort prefix. -/
def errorMap (ops : Ops) (state : State)
 (reply : core.result.Result Unit aspis_r1_cost_probe.verifier.Error) : Run PR :=
 match reply with
 | .Ok unit => pure (.Ok unit)
 | .Err err => do
  let converted ← NJU_Log.record (.error state err) (ops.op44 err)
  pure (.Err converted)
theorem errorMap_result (ops : Ops) (state : State)
 (reply : core.result.Result Unit aspis_r1_cost_probe.verifier.Error) :
 (errorMap ops state reply).result = core.result.Result.map_err
  (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error PE) reply ops.op44 := by
 cases reply with
 | Ok unit => rfl
 | Err err =>
  unfold errorMap
  rw [NJU_Log.erase_bind]
  rfl
#print errorMap_result
#print axioms errorMap_result
end NLE_Owned

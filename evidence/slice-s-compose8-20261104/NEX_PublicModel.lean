import NEX_TerminalOracle
import S6CurrentCodecInstallationV1
set_option autoImplicit false
noncomputable section
namespace NEX_PublicModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Statement := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev PE := AdapterRw.solana_program_error.ProgramError

def run (bytes : Slice U8) : Result (core.result.Result Statement PE) := do
  let reply ← NEX_TerminalOracle.run decode_terminal_common_boxed_v1
    decode_transfer_statement_boxed_v1 decode_withdrawal_statement_boxed_v1
    validate_pool_v1_pair_forest_terminal_statement_v1 bytes
  match reply with
  | .Ok value => ok (.Ok (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 value))
  | .Err _ => ok (.Err .InvalidAccountData)

/-- Endpoint is the coherent installed codec (op47), not a fresh decoder model.
The terminal child and carrier laws are reused. Native forwarding/Box evidence
must independently supply the ruling-(y)/(aa) part of the hybrid certificate. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run bytes,state,([] : List Unit)) =
    (AspisS6CurrentCodecInstallation.decode bytes,state,[]) := by
  have child := congrArg (fun x => x.1) (NEX_TerminalOracle.result_state_effects bytes state)
  dsimp only at child
  unfold run AspisS6CurrentCodecInstallation.decode
  rw [child,AspisS6CurrentCodecInstallation.boxed_eq]
  unfold AspisS6CurrentCodecInstallation.boxOps AspisS6CurrentCodecInstallation.rawDecoder
  dsimp only
  cases run : decode_pool_v1_pair_forest_terminal_statement_v1 bytes with
  | fail e => simp only [run,AspisS6OuterNativeOps.resultMap,bind_tc_fail]
  | div => simp only [run,AspisS6OuterNativeOps.resultMap,bind_tc_div]
  | ok reply => cases reply <;> simp only [run,AspisS6OuterNativeOps.resultMap,AspisS6CurrentCodecInstallation.mapBoth,bind_tc_ok]

#print axioms result_state_effects
#print axioms AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1
end NEX_PublicModel

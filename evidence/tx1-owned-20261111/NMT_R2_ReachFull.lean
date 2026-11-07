import NMT_R2_ReachCommon
set_option autoImplicit false
noncomputable section
namespace NMT_R2_Reach
open Aeneas Aeneas.Std

def full (child : SnapshotCall) (bytes : Slice U8) :=
 NFY_NEX_TerminalOracle.run (common child)
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 bytes

theorem full_source (bytes : Slice U8) : full snapshot bytes =
 AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes := by
 unfold full
 rw [show common snapshot = AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 from funext common_source]
 exact congrArg (fun x => x.1) (NFY_NEX_TerminalOracle.result_state_effects bytes ())

def reaches (bytes : Slice U8) : Bool :=
 match full markSnapshot bytes with | .div => true | _ => false

theorem reaches_iff (bytes : Slice U8) : reaches bytes = true ↔ full markSnapshot bytes = .div := by
 unfold reaches
 cases full markSnapshot bytes <;> simp
#print axioms full_source
#print axioms reaches_iff
end NMT_R2_Reach
end

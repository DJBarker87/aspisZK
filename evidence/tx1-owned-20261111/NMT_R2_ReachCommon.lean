import NMT_R2_ReachLane
set_option autoImplicit false
noncomputable section
namespace NMT_R2_Reach
open Aeneas Aeneas.Std

def common (child : SnapshotCall) (bytes : Slice U8) :=
 NGF_NEX_CommonOracle.run AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical (lane child) bytes

theorem common_source (bytes : Slice U8) : common snapshot bytes =
 AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1 bytes := by
 unfold common
 rw [show lane snapshot = AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1 from funext lane_source]
 exact congrArg (fun x => x.1) (NGF_NEX_CommonOracle.result_state_effects bytes ())
#print axioms common_source
end NMT_R2_Reach
end

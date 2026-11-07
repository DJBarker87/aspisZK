import NMT_R2_ReachLate
set_option autoImplicit false
noncomputable section
namespace NMT_R2_Reach
open Aeneas Aeneas.Std

def lane (child : SnapshotCall) (bytes : Slice U8) :=
 NGF_NEX_LaneOracle.run (late child) bytes

theorem lane_source (bytes : Slice U8) : lane snapshot bytes =
 AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1 bytes := by
 unfold lane
 rw [show late snapshot = AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 from funext late_source]
 exact congrArg (fun x => x.1) (NGF_NEX_LaneOracle.result_state_effects bytes ())
#print axioms lane_source
end NMT_R2_Reach
end

import NMT_R2_ReachSnapshot
set_option autoImplicit false
noncomputable section
namespace NMT_R2_Reach
open Aeneas Aeneas.Std

def late (child : SnapshotCall) (bytes : Slice U8) :=
 NGF_NEX_LateOracle.run child
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes

theorem late_source (bytes : Slice U8) : late snapshot bytes =
 AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 bytes := by
 exact congrArg (fun x => x.1) (NGF_NEX_LateOracle.result_state_effects bytes ())
#print axioms late_source
end NMT_R2_Reach
end

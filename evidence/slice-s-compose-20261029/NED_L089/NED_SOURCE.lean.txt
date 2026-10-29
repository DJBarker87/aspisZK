import NED_DigestCohorts
set_option autoImplicit false
noncomputable section
namespace NED_EncoderLoopCohorts
open Aeneas Aeneas.Std Result
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 8#usize))

theorem after_body (iter : Iter) (out : Array U8 688#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body iter out =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body iter out := by rfl

theorem after_loop (iter : Iter) (out : Array U8 688#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
  have body : (fun (p : Iter × Array U8 688#usize) => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body p.1 p.2) =
      (fun p => AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body p.1 p.2) := by
    funext p; exact after_body p.1 p.2
  rw [body]

theorem live_body (iter : Iter) (out : Slice U8) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body iter out =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body iter out := by rfl

theorem live_loop (iter : Iter) (out : Slice U8) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop iter out =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop iter out := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop
  have body : (fun (p : Iter × Slice U8) => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body p.1 p.2) =
      (fun p => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body p.1 p.2) := by
    funext p; exact live_body p.1 p.2
  rw [body]

#print axioms after_body
#print axioms after_loop
#print axioms live_body
#print axioms live_loop
end NED_EncoderLoopCohorts

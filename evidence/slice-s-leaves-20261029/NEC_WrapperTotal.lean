import NEC_AfterstateBox
import NEC_LiveBox
import NEC_LaneBox
import NEC_TransferDecode
import NEC_WithdrawalDecode
set_option autoImplicit false
namespace NEC_WrapperTotal
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1

theorem afterstate (bytes : Slice U8) :
 pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes=
 (do let reply ← pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes
     NEC_AfterstateBox.reference reply) := by
 cases child : pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes with
 | fail error=>unfold pair_tree_profile.decode_pair_afterstate_boxed_v1;rw [child];rfl
 | div=>unfold pair_tree_profile.decode_pair_afterstate_boxed_v1;rw [child];rfl
 | ok reply=>rw [NEC_AfterstateBox.emitted bytes reply child];rfl

theorem live (bytes : Slice U8) :
 pair_tree_profile.decode_pair_live_snapshot_boxed_v1 bytes=
 (do let reply ← pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes
     NEC_LiveBox.reference reply) := by
 cases child : pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes with
 | fail error=>unfold pair_tree_profile.decode_pair_live_snapshot_boxed_v1;rw [child];rfl
 | div=>unfold pair_tree_profile.decode_pair_live_snapshot_boxed_v1;rw [child];rfl
 | ok reply=>rw [NEC_LiveBox.emitted bytes reply child];rfl

theorem lane (bytes : Slice U8) :
 pair_forest_terminal.decode_lane_transition_boxed_v1 bytes=
 (do let reply ← pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 bytes
     NEC_LaneBox.reference reply) := by
 cases child : pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 bytes with
 | fail error=>unfold pair_forest_terminal.decode_lane_transition_boxed_v1;rw [child];rfl
 | div=>unfold pair_forest_terminal.decode_lane_transition_boxed_v1;rw [child];rfl
 | ok reply=>rw [NEC_LaneBox.emitted bytes reply child];rfl

theorem transfer (common : NEC_TransferDecode.Common) (bytes : Slice U8) :
 pair_forest_terminal.decode_transfer_statement_boxed_v1 common bytes=
 (do let reply ← payment_relation.decode_pool_v1_private_transfer_public_v1 bytes
     NEC_TransferDecode.reference common reply) := by
 cases child : payment_relation.decode_pool_v1_private_transfer_public_v1 bytes with
 | fail error=>unfold pair_forest_terminal.decode_transfer_statement_boxed_v1;rw [child];rfl
 | div=>unfold pair_forest_terminal.decode_transfer_statement_boxed_v1;rw [child];rfl
 | ok reply=>rw [NEC_TransferDecode.emitted common bytes reply child];rfl

theorem withdrawal (common : NEC_WithdrawalDecode.Common) (bytes : Slice U8) :
 pair_forest_terminal.decode_withdrawal_statement_boxed_v1 common bytes=
 (do let reply ← payment_relation.decode_pool_v1_withdrawal_public_v1 bytes
     NEC_WithdrawalDecode.reference common reply) := by
 cases child : payment_relation.decode_pool_v1_withdrawal_public_v1 bytes with
 | fail error=>unfold pair_forest_terminal.decode_withdrawal_statement_boxed_v1;rw [child];rfl
 | div=>unfold pair_forest_terminal.decode_withdrawal_statement_boxed_v1;rw [child];rfl
 | ok reply=>rw [NEC_WithdrawalDecode.emitted common bytes reply child];rfl

#print axioms afterstate
#print axioms live
#print axioms lane
#print axioms transfer
#print axioms withdrawal
end NEC_WrapperTotal

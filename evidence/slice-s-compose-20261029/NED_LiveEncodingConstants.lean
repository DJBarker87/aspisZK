import NED_AfterEncodingConstants
set_option autoImplicit false
namespace NED_LiveEncodingConstants

theorem magic : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
  rfl

theorem version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
  rfl

theorem size : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES =
    800#usize := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  rfl

theorem depth : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH := by
  simp only [AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH,
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH,
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_TREE_DEPTH]

theorem note_depth : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
  rw [depth]

theorem sentinel : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE
  rfl

theorem format : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
  rw [depth,note_depth,sentinel]
  simp only [NED_AfterEncodingConstants.storage_version]

#print axioms magic
#print axioms version
#print axioms size
#print axioms depth
#print axioms note_depth
#print axioms sentinel
#print axioms format
end NED_LiveEncodingConstants

import NED_LiveEncodingConstants
import NED_RawLateTail
set_option autoImplicit false
namespace NED_LateEncodingConstants

theorem magic : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
  rfl

theorem version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
  rfl

theorem items : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
  rfl

theorem header : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
  rfl

theorem live_bytes : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES := by
  rw [NED_LiveEncodingConstants.size]
  unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  rfl

theorem after_bytes : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES := by
  simp only [AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES]

theorem size_eq : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  rw [header,live_bytes,after_bytes]

theorem size : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES =
    Aeneas.Std.Result.ok 1520#usize := by
  rw [size_eq,AspisR1.JFs_LateConstants.size]

#print axioms magic
#print axioms version
#print axioms items
#print axioms header
#print axioms live_bytes
#print axioms after_bytes
#print axioms size_eq
#print axioms size
end NED_LateEncodingConstants

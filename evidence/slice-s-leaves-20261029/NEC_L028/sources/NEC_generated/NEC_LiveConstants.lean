import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NEC_LiveConstants
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

def binding : Array U8 32#usize := Array.make 32#usize
 [65#u8,83#u8,80#u8,80#u8,65#u8,73#u8,82#u8,49#u8,
  1#u8,20#u8,21#u8,7#u8,1#u8,1#u8,1#u8,1#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

theorem binding_value : pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING=ok binding := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
 rfl

theorem magic : pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val=
 [65#u8,83#u8,80#u8,76#u8,73#u8,86#u8,69#u8,49#u8] := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
 rfl

theorem version : pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION=1#u8 := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
 rfl

theorem live_width : pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES=800#usize := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
 rfl

theorem late_width : pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES=ok 1520#usize := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
 rfl

theorem after_width : pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES=ok 688#usize := by
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
 rfl

#print axioms binding_value
#print axioms magic
#print axioms version
#print axioms live_width
#print axioms late_width
#print axioms after_width
end NEC_LiveConstants

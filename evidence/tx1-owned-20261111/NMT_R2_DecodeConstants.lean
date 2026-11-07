import NMT_R2_SmallAdd
set_option autoImplicit false
namespace NMT_R2_DecodeConstants
open Aeneas Aeneas.Std
/-- Only the three small size summands are normalized; no byte buffer or
concrete decoder execution is evaluated. -/
theorem terminal_size :
 AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES =
 .ok 1880#usize := by
 simp [AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES,
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES,
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
  AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
  AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,
  AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES]
 refine ⟨832#usize,?_,688#usize,?_,1520#usize,?_,1664#usize,?_,?_⟩ <;> apply NMT_R2_SmallAdd.checked_add <;> rfl
#print axioms terminal_size
end NMT_R2_DecodeConstants

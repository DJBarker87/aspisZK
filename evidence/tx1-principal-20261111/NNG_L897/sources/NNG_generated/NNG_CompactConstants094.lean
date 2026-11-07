import NNG_Tree094
set_option autoImplicit false
namespace AspisR1.NNG_CompactConstants094
open Aeneas Aeneas.Std Result NMT_tx1
/-- The finite scalar offset expression has no buffer or recurrence cells. -/
theorem folded : compact.OFF_FOLDED_ROOT=ok 7751#usize := by
 unfold compact.OFF_FOLDED_ROOT compact.OFF_ROUND0 compact.OFF_INACTIVE compact.OFF_Y1
  compact.COMPACT_Y1 compact.COMPACT_SEMANTIC compact.SEMANTIC_COMPACT_VALUES
  compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES compact.OFF_SEMANTIC compact.HEADER
 rfl
#print axioms folded

theorem round1 : compact.OFF_ROUND1=ok 7783#usize := by
 unfold compact.OFF_ROUND1
 rw [folded]
 rfl
#print axioms round1
end AspisR1.NNG_CompactConstants094

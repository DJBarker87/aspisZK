import NNG_Tree094
import NNG_ScalarOps094
set_option autoImplicit false
namespace AspisR1.NNG_CompactConstants094
open Aeneas Aeneas.Std Result NMT_tx1
/-- The finite scalar offset expression has no buffer or recurrence cells. -/
theorem folded : compact.OFF_FOLDED_ROOT=ok 7751#usize := by
 unfold compact.OFF_FOLDED_ROOT compact.OFF_ROUND0 compact.OFF_INACTIVE compact.OFF_Y1
  compact.COMPACT_Y1 compact.COMPACT_SEMANTIC compact.SEMANTIC_COMPACT_VALUES
  compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES compact.OFF_SEMANTIC compact.HEADER
 simp only [bind_tc_ok,
  NNG_ScalarOps094.mul 10#usize 28#usize 280#usize rfl,
  NNG_ScalarOps094.add 1#usize 280#usize 281#usize rfl,
  NNG_ScalarOps094.add 87#usize 29#usize 116#usize rfl,
  NNG_ScalarOps094.add 281#usize 116#usize 397#usize rfl,
  NNG_ScalarOps094.add 397#usize 29#usize 426#usize rfl,
  NNG_ScalarOps094.mul 16#usize 426#usize 6816#usize rfl,
  NNG_ScalarOps094.mul 29#usize 32#usize 928#usize rfl,
  NNG_ScalarOps094.add 12903#usize 928#usize 13831#usize rfl,
  NNG_ScalarOps094.sub 13831#usize 6816#usize 7015#usize (by decide) rfl,
  NNG_ScalarOps094.add 16#usize 7015#usize 7031#usize rfl,
  NNG_ScalarOps094.mul 29#usize 16#usize 464#usize rfl,
  NNG_ScalarOps094.add 7031#usize 464#usize 7495#usize rfl,
  NNG_ScalarOps094.add 7495#usize 32#usize 7527#usize rfl,
  NNG_ScalarOps094.add 7527#usize 224#usize 7751#usize rfl]

#print axioms folded

theorem round1 : compact.OFF_ROUND1=ok 7783#usize := by
 unfold compact.OFF_ROUND1
 rw [folded,bind_tc_ok]
 exact NNG_ScalarOps094.add 7751#usize 32#usize 7783#usize rfl
#print axioms round1
end AspisR1.NNG_CompactConstants094

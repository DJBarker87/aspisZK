import NNG_CompactBase094
set_option autoImplicit false
namespace AspisR1.NNG_CompactConstants094
open Aeneas Aeneas.Std
theorem semantic : NMT_tx1.compact.COMPACT_SEMANTIC = .ok 7015#usize := by
 unfold NMT_tx1.compact.COMPACT_SEMANTIC
 unfold NMT_tx1.compact.LOGICAL_SEMANTIC
 simp only [AspisR1.NNG_CompactBase094.semantic,
  AspisR1.NNG_CompactBase094.values,
  (AspisR1.NNG_ScalarOps094.mul 16#usize 426#usize 6816#usize (by change 16 * 426 = 6816; rw [Nat.mul_comm])),
  (AspisR1.NNG_ScalarOps094.sub 13831#usize 6816#usize 7015#usize (by decide) (by change 13831 - 6816 = 7015; omega)),
  bind_tc_ok]
#print axioms semantic
theorem y1 : NMT_tx1.compact.OFF_Y1 = .ok 7031#usize := by
 unfold NMT_tx1.compact.OFF_Y1
 unfold NMT_tx1.compact.OFF_SEMANTIC NMT_tx1.compact.HEADER
 simp only [semantic,
  (AspisR1.NNG_ScalarOps094.add 16#usize 7015#usize 7031#usize rfl),
  bind_tc_ok]
#print axioms y1
theorem inactive : NMT_tx1.compact.OFF_INACTIVE = .ok 7495#usize := by
 unfold NMT_tx1.compact.OFF_INACTIVE
 unfold NMT_tx1.compact.COMPACT_Y1
 simp only [y1,
  (AspisR1.NNG_ScalarOps094.mul 29#usize 16#usize 464#usize rfl),
  (AspisR1.NNG_ScalarOps094.add 7031#usize 464#usize 7495#usize rfl),
  bind_tc_ok]
#print axioms inactive
theorem round0 : NMT_tx1.compact.OFF_ROUND0 = .ok 7527#usize := by
 unfold NMT_tx1.compact.OFF_ROUND0
 simp only [inactive,
  (AspisR1.NNG_ScalarOps094.add 7495#usize 32#usize 7527#usize rfl),
  bind_tc_ok]
#print axioms round0
theorem folded : NMT_tx1.compact.OFF_FOLDED_ROOT = .ok 7751#usize := by
 unfold NMT_tx1.compact.OFF_FOLDED_ROOT
 simp only [round0,
  (AspisR1.NNG_ScalarOps094.add 7527#usize 224#usize 7751#usize rfl),
  bind_tc_ok]
#print axioms folded
theorem round1 : NMT_tx1.compact.OFF_ROUND1 = .ok 7783#usize := by
 unfold NMT_tx1.compact.OFF_ROUND1
 simp only [folded,
  (AspisR1.NNG_ScalarOps094.add 7751#usize 32#usize 7783#usize rfl),
  bind_tc_ok]
#print axioms round1

end AspisR1.NNG_CompactConstants094

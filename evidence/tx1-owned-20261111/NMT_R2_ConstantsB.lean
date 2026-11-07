import NMT_R2_ConstantsA
set_option autoImplicit false
namespace NMT_R2_ConstantsB
open Aeneas Aeneas.Std
theorem semantic : AdapterRw.aspis_r1_cost_probe.compact.COMPACT_SEMANTIC = .ok 7015#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.COMPACT_SEMANTIC
 unfold AdapterRw.aspis_r1_cost_probe.compact.LOGICAL_SEMANTIC
 simp only [NMT_R2_ConstantsA.semantic,
  NMT_R2_ConstantsA.values,
  (NMT_R2_ScalarArithmetic.mul 16#usize 426#usize 6816#usize (by change 16 * 426 = 6816; rw [Nat.mul_comm]; rfl)),
  (NMT_R2_ScalarArithmetic.sub 13831#usize 6816#usize 7015#usize (by decide) rfl),
  bind_tc_ok]
#print axioms semantic
theorem y1 : AdapterRw.aspis_r1_cost_probe.compact.OFF_Y1 = .ok 7031#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_Y1
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_SEMANTIC AdapterRw.aspis_r1_cost_probe.compact.HEADER
 simp only [semantic,
  (NMT_R2_SmallAdd.checked_add 16#usize 7015#usize 7031#usize rfl),
  bind_tc_ok]
#print axioms y1
theorem inactive : AdapterRw.aspis_r1_cost_probe.compact.OFF_INACTIVE = .ok 7495#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_INACTIVE
 unfold AdapterRw.aspis_r1_cost_probe.compact.COMPACT_Y1
 simp only [y1,
  (NMT_R2_ScalarArithmetic.mul 29#usize 16#usize 464#usize rfl),
  (NMT_R2_SmallAdd.checked_add 7031#usize 464#usize 7495#usize rfl),
  bind_tc_ok]
#print axioms inactive
theorem round0 : AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND0 = .ok 7527#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND0
 simp only [inactive,
  (NMT_R2_SmallAdd.checked_add 7495#usize 32#usize 7527#usize rfl),
  bind_tc_ok]
#print axioms round0
theorem folded : AdapterRw.aspis_r1_cost_probe.compact.OFF_FOLDED_ROOT = .ok 7751#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_FOLDED_ROOT
 simp only [round0,
  (NMT_R2_SmallAdd.checked_add 7527#usize 224#usize 7751#usize rfl),
  bind_tc_ok]
#print axioms folded
theorem round1 : AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND1 = .ok 7783#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND1
 simp only [folded,
  (NMT_R2_SmallAdd.checked_add 7751#usize 32#usize 7783#usize rfl),
  bind_tc_ok]
#print axioms round1
theorem final : AdapterRw.aspis_r1_cost_probe.compact.OFF_FINAL = .ok 8007#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_FINAL
 simp only [round1,
  (NMT_R2_SmallAdd.checked_add 7783#usize 224#usize 8007#usize rfl),
  bind_tc_ok]
#print axioms final

end NMT_R2_ConstantsB

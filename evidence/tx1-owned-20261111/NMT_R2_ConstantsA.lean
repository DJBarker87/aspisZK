import NMT_R2_SmallAdd
import NMT_R2_ScalarArithmetic
set_option autoImplicit false
namespace NMT_R2_ConstantsA
open Aeneas Aeneas.Std
theorem nodes : AdapterRw.aspis_r1_cost_probe.compact.MAX_NODES = .ok 914#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.MAX_NODES
 simp only [(NMT_R2_SmallAdd.checked_add 146#usize 172#usize 318#usize rfl),
  (NMT_R2_ScalarArithmetic.mul 2#usize 318#usize 636#usize (by change 2 * 318 = 636; rw [Nat.mul_comm]; rfl)),
  (NMT_R2_SmallAdd.checked_add 128#usize 150#usize 278#usize rfl),
  (NMT_R2_SmallAdd.checked_add 636#usize 278#usize 914#usize rfl),
  bind_tc_ok]
#print axioms nodes
theorem semantic : AdapterRw.aspis_r1_cost_probe.verifier.SEMANTIC_BYTES = .ok 13831#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.verifier.SEMANTIC_BYTES
 simp only [(NMT_R2_ScalarArithmetic.mul 29#usize 32#usize 928#usize (by change 29 * 32 = 928; rw [Nat.mul_comm]; rfl)),
  (NMT_R2_SmallAdd.checked_add 12903#usize 928#usize 13831#usize rfl),
  bind_tc_ok]
#print axioms semantic
theorem values : AdapterRw.aspis_r1_cost_probe.compact.SEMANTIC_COMPACT_VALUES = .ok 426#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.SEMANTIC_COMPACT_VALUES
 simp only [(NMT_R2_ScalarArithmetic.mul 10#usize 28#usize 280#usize (by change 10 * 28 = 280; rw [Nat.mul_comm]; rfl)),
  (NMT_R2_SmallAdd.checked_add 1#usize 280#usize 281#usize rfl),
  (NMT_R2_SmallAdd.checked_add 87#usize 29#usize 116#usize rfl),
  (NMT_R2_SmallAdd.checked_add 281#usize 116#usize 397#usize rfl),
  (NMT_R2_SmallAdd.checked_add 397#usize 29#usize 426#usize rfl),
  bind_tc_ok]
#print axioms values

end NMT_R2_ConstantsA

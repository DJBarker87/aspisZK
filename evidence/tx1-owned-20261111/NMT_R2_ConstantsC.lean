import NMT_R2_ConstantsB
set_option autoImplicit false
namespace NMT_R2_ConstantsC
open Aeneas Aeneas.Std
theorem opening : AdapterRw.aspis_r1_cost_probe.compact.OPENING = .ok 832#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OPENING
 simp only [(NMT_R2_SmallAdd.checked_add 480#usize 128#usize 608#usize rfl),
  (NMT_R2_SmallAdd.checked_add 608#usize 32#usize 640#usize rfl),
  (NMT_R2_SmallAdd.checked_add 640#usize 32#usize 672#usize rfl),
  (NMT_R2_SmallAdd.checked_add 672#usize 128#usize 800#usize rfl),
  (NMT_R2_SmallAdd.checked_add 800#usize 32#usize 832#usize rfl),
  bind_tc_ok]
#print axioms opening
theorem openings : AdapterRw.aspis_r1_cost_probe.compact.OFF_OPENINGS = .ok 10055#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_OPENINGS
 unfold AdapterRw.aspis_r1_cost_probe.compact.FINAL_LEN
 simp only [NMT_R2_ConstantsB.final,
  (NMT_R2_ScalarArithmetic.mul 64#usize 32#usize 2048#usize rfl),
  (NMT_R2_SmallAdd.checked_add 8007#usize 2048#usize 10055#usize rfl),
  bind_tc_ok]
#print axioms openings
theorem fixed : AdapterRw.aspis_r1_cost_probe.compact.FIXED = .ok 28359#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.compact.FIXED
 unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_NODES AdapterRw.aspis_r1_cost_probe.compact.QUERIES
 simp only [opening,
  openings,
  (NMT_R2_ScalarArithmetic.mul 22#usize 832#usize 18304#usize (by change 22 * 832 = 18304; rw [Nat.mul_comm]; rfl)),
  (NMT_R2_SmallAdd.checked_add 10055#usize 18304#usize 28359#usize rfl),
  bind_tc_ok]
#print axioms fixed
theorem proof : AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = .ok 57607#usize := by
 unfold AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES
 unfold AdapterRw.aspis_r1_cost_probe.compact.PROOF_BYTES AdapterRw.aspis_r1_cost_probe.compact.MAX_PROOF
 simp only [NMT_R2_ConstantsA.nodes,
  fixed,
  (NMT_R2_ScalarArithmetic.mul 32#usize 914#usize 29248#usize (by change 32 * 914 = 29248; rw [Nat.mul_comm]; rfl)),
  (NMT_R2_SmallAdd.checked_add 28359#usize 29248#usize 57607#usize rfl),
  bind_tc_ok]
#print axioms proof

end NMT_R2_ConstantsC

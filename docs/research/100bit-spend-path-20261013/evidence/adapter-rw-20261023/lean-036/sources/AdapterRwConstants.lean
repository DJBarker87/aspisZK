import AdapterRwScalar
set_option autoImplicit false
namespace AspisR1.AdapterRw.Constants
open Aeneas Aeneas.Std Result

theorem constant_aspis_r1_cost_probe_compact_MAX_NODES : AdapterRw.aspis_r1_cost_probe.compact.MAX_NODES = ok 914#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.MAX_NODES
  rw [Scalar.add_eq 146#usize 172#usize 318#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.mul_eq 2#usize 318#usize 636#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 128#usize 150#usize 278#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 636#usize 278#usize 914#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OPENING : AdapterRw.aspis_r1_cost_probe.compact.OPENING = ok 832#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OPENING
  rw [Scalar.add_eq 480#usize 128#usize 608#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 608#usize 32#usize 640#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 640#usize 32#usize 672#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 672#usize 128#usize 800#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 800#usize 32#usize 832#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_QUERIES : AdapterRw.aspis_r1_cost_probe.compact.QUERIES = 22#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.QUERIES
  rfl

theorem constant_aspis_r1_cost_probe_compact_FINAL_LEN : AdapterRw.aspis_r1_cost_probe.compact.FINAL_LEN = 64#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.FINAL_LEN
  rfl

theorem constant_aspis_r1_cost_probe_compact_SEMANTIC_COMPACT_VALUES : AdapterRw.aspis_r1_cost_probe.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.SEMANTIC_COMPACT_VALUES
  rw [Scalar.mul_eq 10#usize 28#usize 280#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 1#usize 280#usize 281#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 87#usize 29#usize 116#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 281#usize 116#usize 397#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 397#usize 29#usize 426#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_verifier_SEMANTIC_BYTES : AdapterRw.aspis_r1_cost_probe.verifier.SEMANTIC_BYTES = ok 13831#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.verifier.SEMANTIC_BYTES
  rw [Scalar.mul_eq 29#usize 32#usize 928#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 12903#usize 928#usize 13831#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_LOGICAL_SEMANTIC : AdapterRw.aspis_r1_cost_probe.compact.LOGICAL_SEMANTIC = ok 13831#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.LOGICAL_SEMANTIC
  rw [constant_aspis_r1_cost_probe_verifier_SEMANTIC_BYTES]
  simp only [bind_tc_ok]
  rfl

theorem constant_aspis_r1_cost_probe_compact_COMPACT_SEMANTIC : AdapterRw.aspis_r1_cost_probe.compact.COMPACT_SEMANTIC = ok 7015#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.COMPACT_SEMANTIC
  rw [constant_aspis_r1_cost_probe_compact_SEMANTIC_COMPACT_VALUES, constant_aspis_r1_cost_probe_compact_LOGICAL_SEMANTIC]
  simp only [bind_tc_ok]
  rw [Scalar.mul_eq 16#usize 426#usize 6816#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.sub_eq 13831#usize 6816#usize 7015#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_SEMANTIC : AdapterRw.aspis_r1_cost_probe.compact.OFF_SEMANTIC = 16#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_SEMANTIC
  rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_Y1 : AdapterRw.aspis_r1_cost_probe.compact.OFF_Y1 = ok 7031#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_Y1
  rw [constant_aspis_r1_cost_probe_compact_COMPACT_SEMANTIC, constant_aspis_r1_cost_probe_compact_OFF_SEMANTIC]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 16#usize 7015#usize 7031#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_COMPACT_Y1 : AdapterRw.aspis_r1_cost_probe.compact.COMPACT_Y1 = ok 464#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.COMPACT_Y1
  rw [Scalar.mul_eq 29#usize 16#usize 464#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_INACTIVE : AdapterRw.aspis_r1_cost_probe.compact.OFF_INACTIVE = ok 7495#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_INACTIVE
  rw [constant_aspis_r1_cost_probe_compact_OFF_Y1, constant_aspis_r1_cost_probe_compact_COMPACT_Y1]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 7031#usize 464#usize 7495#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_ROUND0 : AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND0 = ok 7527#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND0
  rw [constant_aspis_r1_cost_probe_compact_OFF_INACTIVE]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 7495#usize 32#usize 7527#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_FOLDED_ROOT : AdapterRw.aspis_r1_cost_probe.compact.OFF_FOLDED_ROOT = ok 7751#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_FOLDED_ROOT
  rw [constant_aspis_r1_cost_probe_compact_OFF_ROUND0]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 7527#usize 224#usize 7751#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_ROUND1 : AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND1 = ok 7783#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND1
  rw [constant_aspis_r1_cost_probe_compact_OFF_FOLDED_ROOT]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 7751#usize 32#usize 7783#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_FINAL : AdapterRw.aspis_r1_cost_probe.compact.OFF_FINAL = ok 8007#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_FINAL
  rw [constant_aspis_r1_cost_probe_compact_OFF_ROUND1]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 7783#usize 224#usize 8007#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_OPENINGS : AdapterRw.aspis_r1_cost_probe.compact.OFF_OPENINGS = ok 10055#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_OPENINGS
  rw [constant_aspis_r1_cost_probe_compact_FINAL_LEN, constant_aspis_r1_cost_probe_compact_OFF_FINAL]
  simp only [bind_tc_ok]
  rw [Scalar.mul_eq 64#usize 32#usize 2048#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 8007#usize 2048#usize 10055#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_OFF_NODES : AdapterRw.aspis_r1_cost_probe.compact.OFF_NODES = ok 28359#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.OFF_NODES
  rw [constant_aspis_r1_cost_probe_compact_OPENING, constant_aspis_r1_cost_probe_compact_QUERIES, constant_aspis_r1_cost_probe_compact_OFF_OPENINGS]
  simp only [bind_tc_ok]
  rw [Scalar.mul_eq 22#usize 832#usize 18304#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 10055#usize 18304#usize 28359#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_FIXED : AdapterRw.aspis_r1_cost_probe.compact.FIXED = ok 28359#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.FIXED
  rw [constant_aspis_r1_cost_probe_compact_OFF_NODES]
  simp only [bind_tc_ok]
  rfl

theorem constant_aspis_r1_cost_probe_compact_MAX_PROOF : AdapterRw.aspis_r1_cost_probe.compact.MAX_PROOF = ok 57607#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.MAX_PROOF
  rw [constant_aspis_r1_cost_probe_compact_MAX_NODES, constant_aspis_r1_cost_probe_compact_FIXED]
  simp only [bind_tc_ok]
  rw [Scalar.mul_eq 32#usize 914#usize 29248#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 28359#usize 29248#usize 57607#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

theorem constant_aspis_r1_cost_probe_compact_PROOF_BYTES : AdapterRw.aspis_r1_cost_probe.compact.PROOF_BYTES = ok 57607#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.compact.PROOF_BYTES
  rw [constant_aspis_r1_cost_probe_compact_MAX_PROOF]
  simp only [bind_tc_ok]
  rfl

theorem constant_aspis_r1_cost_probe_verifier_PROOF_BYTES : AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = ok 57607#usize := by
  unfold AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES
  rw [constant_aspis_r1_cost_probe_compact_PROOF_BYTES]
  simp only [bind_tc_ok]
  rfl

theorem constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES = 680#usize := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  rfl

theorem constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES (ops : AdapterRw.Ops) : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops = ok 688#usize := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  rw [constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES]
  simp only [bind_tc_ok]
  rw [Scalar.add_eq 8#usize 680#usize 688#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  try rfl

#print axioms constant_aspis_r1_cost_probe_compact_MAX_NODES
#print axioms constant_aspis_r1_cost_probe_compact_OPENING
#print axioms constant_aspis_r1_cost_probe_compact_QUERIES
#print axioms constant_aspis_r1_cost_probe_compact_FINAL_LEN
#print axioms constant_aspis_r1_cost_probe_compact_SEMANTIC_COMPACT_VALUES
#print axioms constant_aspis_r1_cost_probe_verifier_SEMANTIC_BYTES
#print axioms constant_aspis_r1_cost_probe_compact_LOGICAL_SEMANTIC
#print axioms constant_aspis_r1_cost_probe_compact_COMPACT_SEMANTIC
#print axioms constant_aspis_r1_cost_probe_compact_OFF_SEMANTIC
#print axioms constant_aspis_r1_cost_probe_compact_OFF_Y1
#print axioms constant_aspis_r1_cost_probe_compact_COMPACT_Y1
#print axioms constant_aspis_r1_cost_probe_compact_OFF_INACTIVE
#print axioms constant_aspis_r1_cost_probe_compact_OFF_ROUND0
#print axioms constant_aspis_r1_cost_probe_compact_OFF_FOLDED_ROOT
#print axioms constant_aspis_r1_cost_probe_compact_OFF_ROUND1
#print axioms constant_aspis_r1_cost_probe_compact_OFF_FINAL
#print axioms constant_aspis_r1_cost_probe_compact_OFF_OPENINGS
#print axioms constant_aspis_r1_cost_probe_compact_OFF_NODES
#print axioms constant_aspis_r1_cost_probe_compact_FIXED
#print axioms constant_aspis_r1_cost_probe_compact_MAX_PROOF
#print axioms constant_aspis_r1_cost_probe_compact_PROOF_BYTES
#print axioms constant_aspis_r1_cost_probe_verifier_PROOF_BYTES
#print axioms constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
#print axioms constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
end AspisR1.AdapterRw.Constants

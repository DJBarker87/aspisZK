import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.AdapterRw.Constants
open Aeneas Aeneas.Std Result

/-- Transitive constant initializers are extracted from shipped Rust. -/
theorem proof_bytes : AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = ok 57607#usize := by
  simp only [AdapterRw.aspis_r1_cost_probe.compact.QUERIES, AdapterRw.aspis_r1_cost_probe.verifier.SEMANTIC_BYTES, AdapterRw.aspis_r1_cost_probe.compact.LOGICAL_SEMANTIC, AdapterRw.aspis_r1_cost_probe.compact.SEMANTIC_COMPACT_VALUES, AdapterRw.aspis_r1_cost_probe.compact.COMPACT_SEMANTIC, AdapterRw.aspis_r1_cost_probe.compact.COMPACT_Y1, AdapterRw.aspis_r1_cost_probe.compact.OPENING, AdapterRw.aspis_r1_cost_probe.compact.OFF_SEMANTIC, AdapterRw.aspis_r1_cost_probe.compact.OFF_Y1, AdapterRw.aspis_r1_cost_probe.compact.OFF_INACTIVE, AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND0, AdapterRw.aspis_r1_cost_probe.compact.OFF_FOLDED_ROOT, AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND1, AdapterRw.aspis_r1_cost_probe.compact.OFF_FINAL, AdapterRw.aspis_r1_cost_probe.compact.FINAL_LEN, AdapterRw.aspis_r1_cost_probe.compact.OFF_OPENINGS, AdapterRw.aspis_r1_cost_probe.compact.OFF_NODES, AdapterRw.aspis_r1_cost_probe.compact.FIXED, AdapterRw.aspis_r1_cost_probe.compact.MAX_NODES, AdapterRw.aspis_r1_cost_probe.compact.MAX_PROOF, AdapterRw.aspis_r1_cost_probe.compact.PROOF_BYTES, AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES, AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES, AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
  scalar_tac

theorem proof_start (ops : AdapterRw.Ops) :
    AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops =
      ok 688#usize := by
  simp only [AdapterRw.aspis_r1_cost_probe.compact.QUERIES, AdapterRw.aspis_r1_cost_probe.verifier.SEMANTIC_BYTES, AdapterRw.aspis_r1_cost_probe.compact.LOGICAL_SEMANTIC, AdapterRw.aspis_r1_cost_probe.compact.SEMANTIC_COMPACT_VALUES, AdapterRw.aspis_r1_cost_probe.compact.COMPACT_SEMANTIC, AdapterRw.aspis_r1_cost_probe.compact.COMPACT_Y1, AdapterRw.aspis_r1_cost_probe.compact.OPENING, AdapterRw.aspis_r1_cost_probe.compact.OFF_SEMANTIC, AdapterRw.aspis_r1_cost_probe.compact.OFF_Y1, AdapterRw.aspis_r1_cost_probe.compact.OFF_INACTIVE, AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND0, AdapterRw.aspis_r1_cost_probe.compact.OFF_FOLDED_ROOT, AdapterRw.aspis_r1_cost_probe.compact.OFF_ROUND1, AdapterRw.aspis_r1_cost_probe.compact.OFF_FINAL, AdapterRw.aspis_r1_cost_probe.compact.FINAL_LEN, AdapterRw.aspis_r1_cost_probe.compact.OFF_OPENINGS, AdapterRw.aspis_r1_cost_probe.compact.OFF_NODES, AdapterRw.aspis_r1_cost_probe.compact.FIXED, AdapterRw.aspis_r1_cost_probe.compact.MAX_NODES, AdapterRw.aspis_r1_cost_probe.compact.MAX_PROOF, AdapterRw.aspis_r1_cost_probe.compact.PROOF_BYTES, AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES, AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES, AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
  scalar_tac

#print axioms proof_bytes
#print axioms proof_start
end AspisR1.AdapterRw.Constants

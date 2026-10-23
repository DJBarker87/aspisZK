import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.AdapterRw.Constants
open Aeneas Aeneas.Std Result

/-- Transitive constant initializers are extracted from shipped Rust. -/
theorem proof_bytes : AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = ok 57607#usize := by
  rfl

theorem proof_start (ops : AdapterRw.Ops) :
    AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops =
      ok 688#usize := by
  rfl

#print axioms proof_bytes
#print axioms proof_start
end AspisR1.AdapterRw.Constants

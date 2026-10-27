import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkConstants
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem proofStart (ops : Ops) :
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=ok 688#usize := by
  unfold aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  rfl
#print axioms proofStart

theorem observer (ops : Ops) : AdapterRw.observer ops=ok none := rfl
#print axioms observer

theorem statementSize (ops : Ops) (common : ops.op19=ok 1520#usize) :
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops=ok 1880#usize := by
  unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
    aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  rw [common,bind_tc_ok]
  rfl
#print axioms statementSize
end AspisR1.JGx_SdkConstants
end

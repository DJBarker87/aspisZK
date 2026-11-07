import NNH_SmallUsize
set_option autoImplicit false
namespace NNH_RequestSize
open Aeneas Aeneas.Std Result AdapterRw

theorem value : aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=.ok 320#usize := by
 unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
 rw [NNH_SmallUsize.mul]
 simp only [bind_tc_ok]
 rw [NNH_SmallUsize.first]
 simp only [bind_tc_ok]
 exact NNH_SmallUsize.last
#print axioms value
end NNH_RequestSize

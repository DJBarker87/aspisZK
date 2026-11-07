import NNH_ValidateFission
set_option autoImplicit false
namespace NNH_RequestSize
open Aeneas Aeneas.Std Result AdapterRw
#print Aeneas.Std.UScalar.mul
#print Aeneas.Std.UScalar.add

theorem value : aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=.ok 320#usize := by
 unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
 simp [UScalar.mul,UScalar.add]
#print axioms value
end NNH_RequestSize

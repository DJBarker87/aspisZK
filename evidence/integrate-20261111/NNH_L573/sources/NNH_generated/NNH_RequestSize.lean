import NNH_ValidateFission
set_option autoImplicit false
namespace NNH_RequestSize
open Aeneas Aeneas.Std Result AdapterRw
#print Aeneas.Std.UScalar.mul
#print Aeneas.Std.UScalar.add

theorem value : aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=.ok 320#usize := by
 unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
 have mul : (3#usize * 32#usize : Result Usize)=.ok 96#usize := by decide
 have first : (8#usize + 96#usize : Result Usize)=.ok 104#usize := by decide
 have last : (104#usize + 216#usize : Result Usize)=.ok 320#usize := by decide
 rw [mul]
 simp only [bind_tc_ok]
 rw [first]
 simp only [bind_tc_ok]
 exact last
#print axioms value
end NNH_RequestSize

import NGL_AuthGuards
set_option autoImplicit false
noncomputable section
namespace NHD_RequestSize
open Aeneas Aeneas.Std Result

theorem request_size :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES =
      ok 320#usize := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  scalar_tac

#print axioms request_size
end NHD_RequestSize

import NGL_AuthGuards
set_option autoImplicit false
noncomputable section
namespace NHD_RequestSize
open Aeneas Aeneas.Std Result

theorem request_size :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES =
      ok 320#usize := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  unfold AdapterRw.aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  have hm := Usize.mul_spec (x := 3#usize) (y := 32#usize) (by scalar_tac)
  obtain ⟨v,hv,veq⟩ := WP.spec_imp_exists hm
  have ve : v = 96#usize := by scalar_tac
  rw [ve] at hv
  rw [hv]
  simp only [bind_tc_ok]
  have ha := Usize.add_spec (x := 8#usize) (y := 96#usize) (by scalar_tac)
  obtain ⟨w,hw,weq⟩ := WP.spec_imp_exists ha
  have we : w = 104#usize := by scalar_tac
  rw [we] at hw
  rw [hw]
  simp only [bind_tc_ok]
  have hb := Usize.add_spec (x := 104#usize) (y := 216#usize) (by scalar_tac)
  obtain ⟨z,hz,zeq⟩ := WP.spec_imp_exists hb
  have ze : z = 320#usize := by scalar_tac
  simpa only [ze] using hz

#print axioms request_size
end NHD_RequestSize

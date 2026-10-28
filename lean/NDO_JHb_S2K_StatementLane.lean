import NDO_JHb_S2K_StatementChecks

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.StatementLane
open AspisR1TerminalDecoder StatementAdmission StatementChecks
open pool_v1.pair_forest_terminal

theorem eq_of_no_difference (a b : U8) (h : ¬ (a != b) = true) : a = b := by
  simpa only [bne_iff_ne,not_not] using h

theorem lane (s : Statement)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 (nullifier s) =
      ok (.Ok (common s).output_lane) := by
  obtain ⟨value,run,same⟩ := raw_lane s h
  rw [eq_of_no_difference value _ same] at run
  exact run

#print axioms eq_of_no_difference
#print axioms lane
end AspisR1.S2K.StatementLane

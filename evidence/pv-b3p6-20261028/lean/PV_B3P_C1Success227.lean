import PV_B3P_Success227
import PV_B3P_P227_13b
import PV_B3P_ClaimSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_terminal_select_c1_227 (claims : Array aspis_core.field.QM31 84#usize) (row : Std.Usize) (hrow : row.val<3) :
    Success (reference_terminal.select_c1_227 claims row) := by
  unfold reference_terminal.select_c1_227
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q1
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q2
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q3
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q4
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q5
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q6
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q7
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q8
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q9
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q10
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q11
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q12
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q13
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q14
  apply bind
  · apply selected_claim_total <;> scalar_tac
  intro q15
  exact ok _

#print axioms total_reference_terminal_select_c1_227

end PV_B3P_Success227

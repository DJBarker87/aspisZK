import NEY_BindingContinuation
set_option autoImplicit false
noncomputable section
namespace NEY_BindingSuccess
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open NEY_BindingContinuation

theorem first_success (s : Statement)
    (accepted : run validate_pool_v1_pair_forest_terminal_statement_v1 validate_result s = ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) := by
  unfold run at accepted
  cases first : validate_pool_v1_pair_forest_terminal_statement_v1 s with
  | fail e => simp only [first,bind_tc_fail] at accepted; cases accepted
  | div => simp only [first,bind_tc_div] at accepted; cases accepted
  | ok outcome =>
    cases outcome with
    | Err e => simp only [first,bind_tc_ok] at accepted; cases accepted
    | Ok unit => cases unit; rfl

/-- Successful binding certifies its statement child on the SAME root input.
This supplies the encoder's reached accepted-statement domain, never a stronger
unproved precondition on emit_result. -/
theorem binding_success (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) := by
  apply first_success s
  rw [NEY_BindingContinuation.result]
  exact accepted

#print axioms first_success
#print axioms binding_success
end NEY_BindingSuccess

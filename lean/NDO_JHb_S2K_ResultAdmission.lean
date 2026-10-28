import NDO_JHb_S2K_ResultNativeSource

/-! SAME successful statement supplies every result-validator guard and child
return. The success of the result validator is derived, never a premise. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultAdmission
open AspisR1TerminalDecoder StatementAdmission StatementChecks
open pool_v1.pair_forest_terminal

abbrev Output := PoolV1PairForestTerminalResultV1

def kind : Statement → pool_v1.historical_anchor.PoolV1TransitionKind
  | .PrivateTransfer _ _ => .PrivateTransfer
  | .Withdrawal _ _ => .Withdrawal

def value (s : Statement) : Output where
  transition_kind := kind s
  master_account := (common s).master_account
  selected_lane_account := (common s).selected_lane_account
  output_lane := (common s).output_lane
  nullifier := nullifier s
  verified_afterstate := (common s).lane_transition.candidate_afterstate

theorem validated (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    validate_result (value s) = ok (.Ok ()) := by
  obtain ⟨master,selected⟩ := zero_guards s accepted
  have lane := StatementLane.lane s accepted
  have encoded := payload s accepted
  simp only [validate_result,value,master,selected,lane,encoded,bind_tc_ok,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    bne_self_eq_false, Bool.false_eq_true,reduceIte]

#print axioms validated
end AspisR1.S2K.ResultAdmission

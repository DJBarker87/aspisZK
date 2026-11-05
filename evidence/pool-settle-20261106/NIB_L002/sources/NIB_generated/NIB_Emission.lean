import NGK_COMBINED_IMPORT

set_option autoImplicit false
noncomputable section
namespace NIB_Emission
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

/-- Invert successful emission itself, rather than assuming statement validity.
The state and statement are those of the reached TX2 emission call. -/
theorem binding_of_success {A E : Type}
    (state after : AspisR1.S2I.ReturnData.State A E) (s : NFY_NEU_EmitModel.Statement)
    (emitted : AspisR1.NFY_JHb_Emit.source
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s = ok (.Ok after)) :
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (AspisR1.S2K.ResultAdmission.value s) = ok (.Ok ()) := by
  rw [← NFY_NEY_EmitComposed.result_state_effects state s] at emitted
  cases h : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (AspisR1.S2K.ResultAdmission.value s) with
  | fail e => simp only [NFY_NEU_EmitModel.run,h,bind_tc_fail] at emitted; cases emitted
  | div => simp only [NFY_NEU_EmitModel.run,h,bind_tc_div] at emitted; cases emitted
  | ok answer =>
    cases answer with
    | Err e => simp only [NFY_NEU_EmitModel.run,h,bind_tc_ok] at emitted; cases emitted
    | Ok u => cases u; rfl
#print axioms binding_of_success

theorem valid_of_success {A E : Type}
    (state after : AspisR1.S2I.ReturnData.State A E) (s : NFY_NEU_EmitModel.Statement)
    (emitted : AspisR1.NFY_JHb_Emit.source
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s = ok (.Ok after)) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()) := by
  exact (NFY_NEY_EmitComposed.reached_encoder s (binding_of_success state after s emitted)).1
#print axioms valid_of_success
end NIB_Emission

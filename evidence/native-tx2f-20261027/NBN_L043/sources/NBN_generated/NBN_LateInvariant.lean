import NBN_StatementDomains
set_option autoImplicit false
noncomputable section
namespace NBN_LateInvariant
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open NBN_StatementResult

theorem value_length (s : NBN_LateTail.Statement) (output : Slice U8) :
    (NBN_LateTail.value s output).length = output.length := by
  unfold NBN_LateTail.value
  cases NBH_LiveValidator.result s.live_snapshot with
  | Err e => rfl
  | Ok u =>
    cases NBH_Validators.afterResult s.candidate_afterstate <;>
      simp only [Slice.length,Slice.setSlice!,List.length_setSlice!]

/-- All 1520-byte caller pre-states; exact SAME successful bytes and length. -/
theorem ready (s : NBN_LateTail.Statement)
    (valid : lateStatus s = .Ok ()) (output : Slice U8) (size : output.length = 1520) :
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s output =
      ok (.Ok (),NBN_LateTail.value s NBN_LateResult.header) := by
  rw [NBN_LateResult.source,if_neg (not_not.mpr size)]
  unfold lateStatus at valid
  split at valid
  · cases valid
  · rename_i index
    rw [if_neg index]
    rw [valid]

theorem statement_ready (s : Statement)
    (valid : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()))
    (output : Slice U8) (size : output.length = 1520) :
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 (common s).lane_transition output =
      ok (.Ok (),NBN_LateTail.value (common s).lane_transition NBN_LateResult.header) ∧
    (NBN_LateTail.value (common s).lane_transition NBN_LateResult.header).length = 1520 := by
  exact ⟨ready _ (NBN_StatementDomains.lane_late s valid).2 output size,
    (value_length _ _).trans NBN_LateResult.header_length⟩

#print axioms value_length
#print axioms ready
#print axioms statement_ready
end NBN_LateInvariant

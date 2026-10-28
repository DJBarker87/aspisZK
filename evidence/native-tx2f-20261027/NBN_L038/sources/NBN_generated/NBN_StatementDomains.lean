import NBN_StatementResult
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_StatementDomains
open Aeneas Aeneas.Std Result
open NBN_StatementResult
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

/-- Same-variant child, not an independently selected successful payment. -/
theorem payment_reached (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    ∃ bytes, payment s = ok (.Ok bytes) ∧ suffix s = .Ok () := by
  rw [source] at accepted
  unfold result at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases hp : payment s with
      | fail e => simp only [hp,bind_tc_fail] at accepted; cases accepted
      | div => simp only [hp,bind_tc_div] at accepted; cases accepted
      | ok r =>
        simp only [hp,bind_tc_ok] at accepted
        cases r with
        | Err e => cases accepted
        | Ok bytes => exact ⟨bytes,rfl,Result.ok.inj accepted⟩

theorem bindings (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    (parts s).1 = (common s).master_account ∧
    (parts s).2.1 = (common s).lane_transition.live_snapshot.deployment_domain ∧
    (common s).lane_transition.live_snapshot.pool = (common s).master_account ∧
    (parts s).2.2.1 = (common s).checkpoint_sequence ∧
    (parts s).2.2.2.1 = (common s).historical_global_anchor := by
  obtain ⟨_,_,h⟩ := payment_reached s accepted
  cases s <;> simp only [suffix,common,parts,NBD_TerminalProjection.parts,
    NBD_TerminalProjection.common] at h ⊢
  all_goals repeat' first
    | (solve | aesop)
    | (split at h <;> try simp_all only [not_not,core.result.Result.reduceCtorEq])

theorem lane_late (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NBN_OutputLane.result (parts s).2.2.2.2.1 = .Ok (common s).output_lane ∧
    lateStatus (common s).lane_transition = .Ok () := by
  obtain ⟨_,_,h⟩ := payment_reached s accepted
  obtain ⟨hp,hd,hl,hs,ha⟩ := bindings s accepted
  simp only [suffix,hp,hd,hl,hs,ha,ne_eq,not_true_eq_false,if_false] at h
  cases lane : NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => simp only [lane] at h; cases h
  | Ok value =>
    simp only [lane] at h
    split at h
    · cases h
    · rename_i same
      have eq : value = (common s).output_lane := not_not.mp same
      subst value
      refine ⟨rfl,?_⟩
      cases late : lateStatus (common s).lane_transition with
      | Err e => simp only [late] at h; cases h
      | Ok u => cases u; rfl

theorem late_children (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 =
      some (common s).lane_transition.candidate_afterstate.next_pair_index ∧
    NBH_LiveValidator.result (common s).lane_transition.live_snapshot = .Ok () ∧
    NBH_Validators.afterResult (common s).lane_transition.candidate_afterstate = .Ok () := by
  have h := (lane_late s accepted).2
  unfold lateStatus at h
  split at h
  · cases h
  · rename_i index
    refine ⟨not_not.mp index,?_⟩
    unfold NBN_LateTail.status at h
    cases live : NBH_LiveValidator.result (common s).lane_transition.live_snapshot with
    | Err e => simp only [live] at h; cases h
    | Ok u =>
      cases u
      simp only [live] at h
      refine ⟨rfl,?_⟩
      cases after : NBH_Validators.afterResult (common s).lane_transition.candidate_afterstate with
      | Err e => simp only [after] at h; cases h
      | Ok u => cases u; rfl

#print axioms payment_reached
#print axioms bindings
#print axioms lane_late
#print axioms late_children
end NBN_StatementDomains

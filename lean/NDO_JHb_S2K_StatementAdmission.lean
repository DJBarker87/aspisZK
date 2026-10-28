import NDO_JHb_S2K_LateAdmission

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.StatementAdmission
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal pool_v1.pair_tree_profile pool_v1.pair_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1

def common : Statement → PoolV1PairForestTerminalCommonV1
  | .PrivateTransfer c _ => c
  | .Withdrawal c _ => c

elab "s2k_unbool" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    for decl in ← Lean.getLCtx do
      let type ← Lean.Meta.whnf decl.type
      if type.isConstOf ``Bool then
        return (← goal.cases decl.fvarId).toList.map (·.mvarId)
    throwError "no boolean variable"

theorem late (s : Statement)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    ∃ before after, encode_pool_v1_pair_late_public_statement_v1
      (common s).lane_transition before = ok (.Ok (),after) := by
  cases s <;> unfold validate_pool_v1_pair_forest_terminal_statement_v1 at h
  all_goals simp only [common,PoolV1PairForestTerminalStatementV1.common,
    statement_public_common,bind_tc_ok,Bind.bind,Aeneas.Std.bind,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at h ⊢
  all_goals generalize Array.repeat 32#usize 0#u8 = zero_bindings at h
  all_goals generalize Array.repeat 1520#usize 0#u8 = late_buffer at h
  all_goals repeat' first
    | (solve | exact ⟨_,_,by assumption⟩)
    | (solve | exact ⟨_,_,rfl⟩)
    | (solve | cases h)
    | (rw [if_pos (show true = true from rfl)] at h)
    | (rw [if_neg (show ¬ (false = true) by decide)] at h)
    | (dsimp only [Aeneas.Std.uncurry] at h)
    | (s2k_unpair <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (s2k_uncase <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | s2k_unbool
    | (split at h)

theorem afterstate (s : Statement)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    validate_verified_afterstate (common s).lane_transition.candidate_afterstate = ok (.Ok ()) := by
  obtain ⟨before,after,run⟩ := late s h
  exact LateAdmission.validated _ before after run

theorem payload (s : Statement)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    encode_pool_v1_pair_verified_afterstate_v1 (common s).lane_transition.candidate_afterstate =
      ok (.Ok (AfterstateEncoding.bytes (common s).lane_transition.candidate_afterstate)) :=
  AfterstateEncoding.encode_exact _ (afterstate s h)

#print axioms late
#print axioms afterstate
#print axioms payload
end AspisR1.S2K.StatementAdmission

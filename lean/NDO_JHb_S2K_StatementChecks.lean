import NDO_JHb_S2K_StatementAdmission

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.StatementChecks
open AspisR1TerminalDecoder StatementAdmission
open pool_v1.pair_forest_terminal pool_v1.pair_tree_profile pool_v1.pair_terminal

theorem zero_guards (s : Statement)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      (common s).master_account (Array.repeat 32#usize 0#u8) = ok false ∧
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      (common s).selected_lane_account (Array.repeat 32#usize 0#u8) = ok false := by
  cases s <;> unfold validate_pool_v1_pair_forest_terminal_statement_v1 at h
  all_goals simp only [common,PoolV1PairForestTerminalStatementV1.common,
    statement_public_common,bind_tc_ok,Bind.bind,Aeneas.Std.bind,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at h ⊢
  all_goals generalize Array.repeat 32#usize 0#u8 = zero_bindings at h ⊢
  all_goals generalize Array.repeat 1520#usize 0#u8 = late_buffer at h
  all_goals repeat' first
    | (solve | exact ⟨by assumption,by assumption⟩)

    | (solve | cases h)
    | (rw [if_pos (show true = true from rfl)] at h)
    | (rw [if_neg (show ¬ (false = true) by decide)] at h)
    | (dsimp only [Aeneas.Std.uncurry] at h)
    | (s2k_unpair <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (s2k_uncase <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | s2k_unbool
    | (split at h)

def nullifier : Statement → Array aspis_core.field.M31 8#usize
  | .PrivateTransfer _ p => p.nullifier
  | .Withdrawal _ p => p.nullifier

theorem raw_lane (s : Statement)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    ∃ value, pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 (nullifier s) =
      ok (.Ok value) ∧ ¬ (value != (common s).output_lane) = true := by
  cases s <;> unfold validate_pool_v1_pair_forest_terminal_statement_v1 at h
  all_goals simp only [nullifier,common,PoolV1PairForestTerminalStatementV1.common,
    statement_public_common,bind_tc_ok,Bind.bind,Aeneas.Std.bind,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at h ⊢
  all_goals generalize Array.repeat 32#usize 0#u8 = zero_bindings at h
  all_goals generalize Array.repeat 1520#usize 0#u8 = late_buffer at h
  all_goals repeat' first
    | (solve | exact ⟨_,by assumption,by assumption⟩)
    | (solve | cases h)
    | (rw [if_pos (show true = true from rfl)] at h)
    | (rw [if_neg (show ¬ (false = true) by decide)] at h)
    | (dsimp only [Aeneas.Std.uncurry] at h)
    | (s2k_unpair <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (s2k_uncase <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | s2k_unbool
    | (split at h)

  all_goals exact ⟨_,rfl,by assumption⟩

#print axioms zero_guards
#print axioms raw_lane
end AspisR1.S2K.StatementChecks

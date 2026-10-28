import NDO_JHb_S2K_StatementAdmission
import AspisR1AdapterReconstruct.Funs
set_option autoImplicit false
namespace AspisR1.JHf_RawStatementDomainGuard
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1.pair_forest_terminal

def paymentDomain : PoolV1PairForestTerminalStatementV1 → Array U8 32#usize
  | .PrivateTransfer _ p=>p.deployment_domain
  | .Withdrawal _ p=>p.deployment_domain

def liveDomain : PoolV1PairForestTerminalStatementV1 → Array U8 32#usize
  | .PrivateTransfer c _=>c.lane_transition.live_snapshot.deployment_domain
  | .Withdrawal c _=>c.lane_transition.live_snapshot.deployment_domain

theorem source (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Ok ())) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      (paymentDomain statement) (liveDomain statement)=ok false := by
  cases statement <;> unfold validate_pool_v1_pair_forest_terminal_statement_v1 at accepted
  all_goals simp only [PoolV1PairForestTerminalStatementV1.common,statement_public_common,
    paymentDomain,liveDomain,bind_tc_ok,Bind.bind,Aeneas.Std.bind,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at accepted ⊢
  all_goals generalize Array.repeat 32#usize 0#u8 = zero_bindings at accepted
  all_goals generalize Array.repeat 1520#usize 0#u8 = late_buffer at accepted
  all_goals repeat' first
    | (solve | assumption)
    | (solve | cases accepted)
    | (rw [if_pos (show true = true from rfl)] at accepted)
    | (rw [if_neg (show ¬ (false = true) by decide)] at accepted)
    | (dsimp only [Aeneas.Std.uncurry] at accepted)
    | (s2k_unpair <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (s2k_uncase <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | s2k_unbool
    | (split at accepted)
#print axioms source
end AspisR1.JHf_RawStatementDomainGuard

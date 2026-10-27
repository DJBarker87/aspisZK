import R1Z.PV_RunJoin_ContinuationProjection
import R1Z.PV_RunJoin_ReservationGuards
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReservationProjection
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 PV_RunJoin_ResultTransport
open PV_RunJoin_ContinuationProjection PV_RunJoin_BindCongruence
variable [ExternalTypes] [ExternalFuns]

/-- Source-state naturality at the sole reservation call. Its premise is an
exact callback projection, not agreement of accepted bits alone. -/
theorem after_checks {S T : Type} (project : S → T)
    (left : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (right : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S)
    (callback : mapR (fun out => (out.1,project out.2))
      (left.«reserve» s context.statement_digest context.mask_nonce) =
      right.«reserve» (project s) context.statement_digest context.mask_nonce) :
    mapR (fun out => (out.1,project out.2))
      (ProverRwOuterAfterChecks.afterChecks left secret hash binding context s) =
    ProverRwOuterAfterChecks.afterChecks right secret hash binding context (project s) := by
  unfold ProverRwOuterAfterChecks.afterChecks
  rw [← callback]
  apply PV_RunJoin_ResultTransport.bind_map
  intro pair
  rcases pair with ⟨accepted,after⟩
  simp only [Aeneas.Std.uncurry]
  cases accepted <;>
    simp only [Bool.false_eq_true,if_false,if_true,map_ok,map_bind,map_if,
      PV_RunJoin_PairElimination.cases_pair]
  repeat' first
    | rfl
    | apply bind_same
      intro value
      try (change (_ × _) at value; rcases value with ⟨value1,value2⟩)
      try simp only [Aeneas.Std.uncurry,map_bind,map_if,map_ok,
        PV_RunJoin_PairElimination.cases_pair,bind_tc_ok]
    | apply if_same
    | split <;> try simp only [map_bind,map_if,map_ok,bind_tc_ok]

#print axioms after_checks
end R1Z.PV_RunJoin_ReservationProjection

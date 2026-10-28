import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_ZeroFactor
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Hash)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  P (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r ← invoke "aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.map_err
      aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
      r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← invoke "aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1" (fun ops =>
        letI : ExternalFuns := ops
        let hash := sourceHash ops hash
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
    invoke "aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d
      self hash context i val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      let hash := sourceHash ops hash
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)

theorem erase_program (ops : ExternalFuns)
  (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Hash)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  erase ops (program self hash context) =
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d _ ops self (sourceHash ops hash) context := by
  unfold program aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro r
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro i
            exact erase_invoke ops _ _
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_ZeroFactor

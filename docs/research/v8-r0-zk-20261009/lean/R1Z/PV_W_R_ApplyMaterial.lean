import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_ApplyMaterial
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) :
  P ((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation) := do
  let r ← invoke "aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1" (fun ops =>
      letI : ExternalFuns := ops
      aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.map_err
      aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
      r ())
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let r2 ← invoke "aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows" (fun ops =>
        letI : ExternalFuns := ops
        aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
    let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTry.branch r2)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      invoke "aspis_prover.state_only_hiding.apply_mask_material_for_layout" (fun ops =>
        letI : ExternalFuns := ops
        aspis_prover.state_only_hiding.apply_mask_material_for_layout trace
        material s val1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
          letI : ExternalFuns := ops
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_hiding.AppliedStateOnlyMasks
          (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
      pure (r3, trace)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
        letI : ExternalFuns := ops
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_hiding.AppliedStateOnlyMasks
        (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
    pure (r2, trace)

theorem erase_program (ops : ExternalFuns)
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) :
  erase ops (program trace material) =
    @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 _ ops trace material := by
  unfold program aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
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
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r2
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro cf1
              try dsimp only
              cases cf1 with
              | Continue val1 =>
                exact erase_invoke ops _ _
              | Break residual =>
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro r3
                  rfl
        | Break residual =>
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro r2
            rfl

#print axioms erase_program
end R1Z.PV_W_R_ApplyMaterial

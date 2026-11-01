import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ApplyMaterial
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op132_OPEN : P ((core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  pool_v1_pair_forest_copy_active_rows_OPEN : P ((core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  apply_mask_material_for_layout_OPEN : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), P (((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation))

structure Compatible (c : Callees) : Prop where
  op132_fixed : FinishedView (c.op132_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)
  pool_v1_pair_forest_copy_active_rows_fixed : FinishedView (c.pool_v1_pair_forest_copy_active_rows_OPEN) (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
  apply_mask_material_for_layout_fixed : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), FinishedView (c.apply_mask_material_for_layout_OPEN trace material cells active) (aspis_prover.state_only_hiding.apply_mask_material_for_layout trace material cells active)

def run
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (c : Callees) : P ((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation) := do
  let r ← c.op132_OPEN
  let r1 ← PV_EVH_Prefix.lift (core.result.Result.map_err
      aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
      r ())
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let r2 ← c.pool_v1_pair_forest_copy_active_rows_OPEN
    let cf1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      c.apply_mask_material_for_layout_OPEN trace
        material s val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_hiding.AppliedStateOnlyMasks
          (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
      pure (r3, trace)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_hiding.AppliedStateOnlyMasks
        (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
    pure (r2, trace)

theorem run_fixed
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (c : Callees) (compatible : Compatible c) :
    FinishedView (run trace material c) (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 trace material) := by
  unfold run aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact compatible.op132_fixed
  · intro r
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact PV_EVH_Prefix.lift_fixed _
    · intro r1
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          let s := alloc.vec.Vec.deref val
          try dsimp only
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.pool_v1_pair_forest_copy_active_rows_fixed
          · intro r2
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact PV_EVH_Prefix.lift_fixed _
            · intro cf1
              try dsimp only
              cases cf1 with
              | Continue val1 =>
                exact compatible.apply_mask_material_for_layout_fixed _ _ _ _
              | Break residual =>
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro r3
                  exact PV_EVH_Prefix.lift_fixed _
        | Break residual =>
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro r2
            exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_ApplyMaterial

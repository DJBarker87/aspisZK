import PV_EVH_Runtime
import PV_EVHB_CallbackEffects
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_ApplyMaterial
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Runtime (Q PartialView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  drop_OPEN : ∀ {T : Type}, T → Q Unit
  op132_OPEN : Q ((core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))

  pool_v1_pair_forest_copy_active_rows_OPEN : Q ((core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  apply_mask_material_for_layout_OPEN : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), Q (((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation))

structure Compatible (c : Callees) : Prop where
  drop_fixed : ∀ {T : Type} (value : T), PartialView (c.drop_OPEN value) (.ok ())
  op132_fixed : PartialView (c.op132_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)

  pool_v1_pair_forest_copy_active_rows_fixed : PartialView (c.pool_v1_pair_forest_copy_active_rows_OPEN) (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
  apply_mask_material_for_layout_fixed : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), PartialView (c.apply_mask_material_for_layout_OPEN trace material cells active) (aspis_prover.state_only_hiding.apply_mask_material_for_layout trace material cells active)

def run
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (c : Callees) : Q ((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation) := do
  let r ← c.op132_OPEN
  let r1 ← PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout r ()
  let cf ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let r2 ← c.pool_v1_pair_forest_copy_active_rows_OPEN
    let cf1 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      c.apply_mask_material_for_layout_OPEN trace
        material s val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_hiding.AppliedStateOnlyMasks
          (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
      pure (r3, trace)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← PV_EVH_Runtime.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_hiding.AppliedStateOnlyMasks
        (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual)
    pure (r2, trace)

theorem run_fixed
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (c : Callees) (compatible : Compatible c) :
    PartialView (run trace material c) (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 trace material) := by
  unfold run aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
  try dsimp only
  apply PV_EVH_Runtime.bind_view
  ·
    exact compatible.op132_fixed
  · intro r
    try dsimp only
    apply PV_EVH_Runtime.bind_view
    ·
      exact PV_EVHB_CallbackEffects.mapErr_view c.drop_OPEN c.drop_OPEN aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout () _
        (fun e => compatible.drop_fixed e) (compatible.drop_fixed ())
    · intro r1
      try dsimp only
      apply PV_EVH_Runtime.bind_view
      ·
        exact PV_EVH_Runtime.lift_view _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          let s := alloc.vec.Vec.deref val
          try dsimp only
          try dsimp only
          apply PV_EVH_Runtime.bind_view
          ·
            exact compatible.pool_v1_pair_forest_copy_active_rows_fixed
          · intro r2
            try dsimp only
            apply PV_EVH_Runtime.bind_view
            ·
              exact PV_EVH_Runtime.lift_view _
            · intro cf1
              try dsimp only
              cases cf1 with
              | Continue val1 =>
                exact compatible.apply_mask_material_for_layout_fixed _ _ _ _
              | Break residual =>
                try dsimp only
                apply PV_EVH_Runtime.bind_view
                ·
                  exact PV_EVH_Runtime.lift_view _
                · intro r3
                  exact PV_EVH_Runtime.lift_view _
        | Break residual =>
          try dsimp only
          apply PV_EVH_Runtime.bind_view
          ·
            exact PV_EVH_Runtime.lift_view _
          · intro r2
            exact PV_EVH_Runtime.lift_view _

#print axioms run_fixed
end PV_EVHB_ApplyMaterial

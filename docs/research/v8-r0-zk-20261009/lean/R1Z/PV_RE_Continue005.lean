import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue005
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1`.
Recursive calls remain the original extracted calls. -/
def continueAfter (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (out : Payload (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)) : Result ((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let r2 ←
      aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      aspis_prover.state_only_hiding.apply_mask_material_for_layout trace
        material s val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_hiding.AppliedStateOnlyMasks
          (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      ok (r3, trace)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_hiding.AppliedStateOnlyMasks
        (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
    ok (r2, trace)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 (trace := trace) (material := material) =
      (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 >>= fun out => continueAfter (trace := trace) (material := material) out) := by
  rw [aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (out : Payload (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1))
    (h : (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1) = .ok out) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 (trace := trace) (material := material) = continueAfter (trace := trace) (material := material) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) (e : Error)
    (h : (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1) = .fail e) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 (trace := trace) (material := material) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    (h : (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1) = .div) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 (trace := trace) (material := material) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue005

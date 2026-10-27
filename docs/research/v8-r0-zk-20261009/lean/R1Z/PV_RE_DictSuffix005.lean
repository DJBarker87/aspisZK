import R1Z.PV_RE_DictSuffix004
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix005
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


end R1Z.PV_RE_DictSuffix005
pv_dict_congr ProverRwFull.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
pv_dict_congr R1Z.PV_RE_DictSuffix005.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix005.continueAfter

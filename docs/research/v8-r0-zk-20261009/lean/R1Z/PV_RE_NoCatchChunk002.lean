import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix004
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.sync_directory`.
Recursive calls remain the original extracted calls. -/
def continueAfter (directory : std.path.Path) (out : Payload (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory)) : Result (core.result.Result Unit std.io.error.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val => std.fs.File.sync_all val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual


end R1Z.PV_RE_NoCatchSuffix004
pv_no_catch_binds ProverRwFull.aspis_prover.state_only_entropy.sync_directory
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix004.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix005
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


end R1Z.PV_RE_NoCatchSuffix005
pv_no_catch_binds ProverRwFull.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix005.continueAfter

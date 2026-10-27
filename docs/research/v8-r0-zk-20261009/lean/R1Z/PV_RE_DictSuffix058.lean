import R1Z.PV_RE_DictSuffix057
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix058
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.no_pole`.
Recursive calls remain the original extracted calls. -/
def continueAfter (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) (out : Payload (host_semantic.lean_copy_row_values compiled.trace lambda)) : Result (core.result.Result Bool r1_wire.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1
    let r2 ←
      core.result.Result.map_err
        host_semantic.no_pole.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s := alloc.vec.Vec.deref val
      let b ← ct_pole.all_slots_clear s val1 chi
      ok (core.result.Result.Ok b)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Bool (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Bool (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_DictSuffix058
pv_dict_congr ProverRwFull.host_semantic.no_pole
pv_dict_congr R1Z.PV_RE_DictSuffix058.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.no_pole
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix058.continueAfter

import R1Z.PV_RE_DictSuffix058
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix059
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.point_claims`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (r1_wire.statement_points point)) : Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize)
    3#usize) r1_wire.Error) := do
  let points := out
  let a ← Array.index_usize points 0#usize
  let r ← host_semantic.claims_at_point columns a
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a1 ← Array.index_usize points 1#usize
    let r1 ← host_semantic.claims_at_point columns a1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a2 ← Array.index_usize points 2#usize
      let r2 ← host_semantic.claims_at_point columns a2
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        ok (core.result.Result.Ok (Array.make 3#usize [ val, val1, val2 ]))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
          (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
      (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_DictSuffix059
pv_dict_congr ProverRwFull.host_semantic.point_claims
pv_dict_congr R1Z.PV_RE_DictSuffix059.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.point_claims
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix059.continueAfter

import R1Z.PV_RE_DictSuffix018
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix019
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.lean_copy_row_values`.
Recursive calls remain the original extracted calls. -/
def continueAfter (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31) (out : Payload (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1)) : Result (core.result.Result (alloc.vec.Vec (Array (Array aspis_core.field.QM31
    2#usize) 2#usize)) r1_wire.Error) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      host_semantic.lean_copy_row_values.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairTraceErrorV1Error
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let q ← aspis_core.field.QM31.ZERO
    let a := Array.repeat 2#usize q
    let a1 := Array.repeat 2#usize a
    let values ←
      alloc.vec.from_elem (core.clone.CloneArray 2#usize (core.clone.CloneArray
        2#usize aspis_core.field.QM31.Insts.CoreCloneClone)) a1 1024#usize
    let a2 := Array.repeat 2#usize 0#usize
    let arity ←
      alloc.vec.from_elem (core.clone.CloneArray 2#usize core.clone.CloneUsize)
        a2 1024#usize
    let count := alloc.vec.Vec.len val
    host_semantic.lean_copy_row_values_loop trace lambda val values arity count
      0#usize
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
      (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_DictSuffix019
pv_dict_congr ProverRwFull.host_semantic.lean_copy_row_values
pv_dict_congr R1Z.PV_RE_DictSuffix019.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_semantic.lean_copy_row_values
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix019.continueAfter

import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue019
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31) :
    host_semantic.lean_copy_row_values (trace := trace) (lambda := lambda) =
      (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1 >>= fun out => continueAfter (trace := trace) (lambda := lambda) out) := by
  rw [host_semantic.lean_copy_row_values]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31) (out : Payload (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1))
    (h : (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1) = .ok out) :
    host_semantic.lean_copy_row_values (trace := trace) (lambda := lambda) = continueAfter (trace := trace) (lambda := lambda) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31) (e : Error)
    (h : (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1) = .fail e) :
    host_semantic.lean_copy_row_values (trace := trace) (lambda := lambda) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31)
    (h : (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1) = .div) :
    host_semantic.lean_copy_row_values (trace := trace) (lambda := lambda) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue019

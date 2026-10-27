import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue058
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) :
    host_semantic.no_pole (compiled := compiled) (lambda := lambda) (chi := chi) =
      (host_semantic.lean_copy_row_values compiled.trace lambda >>= fun out => continueAfter (compiled := compiled) (lambda := lambda) (chi := chi) out) := by
  rw [host_semantic.no_pole]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) (out : Payload (host_semantic.lean_copy_row_values compiled.trace lambda))
    (h : (host_semantic.lean_copy_row_values compiled.trace lambda) = .ok out) :
    host_semantic.no_pole (compiled := compiled) (lambda := lambda) (chi := chi) = continueAfter (compiled := compiled) (lambda := lambda) (chi := chi) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) (e : Error)
    (h : (host_semantic.lean_copy_row_values compiled.trace lambda) = .fail e) :
    host_semantic.no_pole (compiled := compiled) (lambda := lambda) (chi := chi) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
    (h : (host_semantic.lean_copy_row_values compiled.trace lambda) = .div) :
    host_semantic.no_pole (compiled := compiled) (lambda := lambda) (chi := chi) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue058

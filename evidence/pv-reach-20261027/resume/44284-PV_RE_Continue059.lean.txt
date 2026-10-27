import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue059
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) :
    host_semantic.point_claims (columns := columns) (point := point) =
      (r1_wire.statement_points point >>= fun out => continueAfter (columns := columns) (point := point) out) := by
  rw [host_semantic.point_claims]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (r1_wire.statement_points point))
    (h : (r1_wire.statement_points point) = .ok out) :
    host_semantic.point_claims (columns := columns) (point := point) = continueAfter (columns := columns) (point := point) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) (e : Error)
    (h : (r1_wire.statement_points point) = .fail e) :
    host_semantic.point_claims (columns := columns) (point := point) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize)
    (h : (r1_wire.statement_points point) = .div) :
    host_semantic.point_claims (columns := columns) (point := point) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue059

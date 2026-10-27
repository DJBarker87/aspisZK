import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue048
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.EncodingDomain.new`.
Recursive calls remain the original extracted calls. -/
def continueAfter  (out : Payload (host_commitment.domain_points)) : Result (core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, levels) ←
      alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new (alloc.vec.Vec
        aspis_core.field.M31)) 9#usize
    let r2 ←
      core.result.Result.map_err
        host_commitment.EncodingDomain.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s := alloc.vec.Vec.deref val
      let r3 ← host_commitment.domain_first_level s
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let levels1 ← alloc.vec.Vec.push levels val1
        let r4 ← host_commitment.domain_append_levels levels1 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok { xy := val, levels := val2 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            host_commitment.EncodingDomain (core.convert.FromSame
            aspis_core.r0.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          host_commitment.EncodingDomain (core.convert.FromSame
          aspis_core.r0.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        host_commitment.EncodingDomain (core.convert.FromSame
        aspis_core.r0.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.EncodingDomain (core.convert.FromSame
      aspis_core.r0.Error) residual

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation  :
    host_commitment.EncodingDomain.new  =
      (host_commitment.domain_points >>= fun out => continueAfter  out) := by
  rw [host_commitment.EncodingDomain.new]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success  (out : Payload (host_commitment.domain_points))
    (h : (host_commitment.domain_points) = .ok out) :
    host_commitment.EncodingDomain.new  = continueAfter  out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure  (e : Error)
    (h : (host_commitment.domain_points) = .fail e) :
    host_commitment.EncodingDomain.new  = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges 
    (h : (host_commitment.domain_points) = .div) :
    host_commitment.EncodingDomain.new  = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue048

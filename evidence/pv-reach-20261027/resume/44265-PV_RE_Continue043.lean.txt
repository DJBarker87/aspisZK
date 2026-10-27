import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue043
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.qm31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self)) : Result ((core.result.Result aspis_core.field.QM31
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_entropy.Profile21SourceExpander) := do
  let (r, self1) := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, self2) ←
      aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let c ← aspis_core.field.CM31.new val val1
      let (r2, self3) ←
        aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self2
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r3, self4) ←
          aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self3
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let c1 ← aspis_core.field.CM31.new val2 val3
          ok (core.result.Result.Ok { c0 := c, c1 }, self4)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_core.field.QM31 (core.convert.FromSame
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
          ok (r4, self4)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.field.QM31 (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
        ok (r3, self3)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      ok (r2, self2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
    ok (r1, self1)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : aspis_prover.state_only_entropy.Profile21SourceExpander) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 (self := self) =
      (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self >>= fun out => continueAfter (self := self) out) := by
  rw [aspis_prover.state_only_entropy.Profile21SourceExpander.qm31]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self))
    (h : (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self) = .ok out) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 (self := self) = continueAfter (self := self) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (e : Error)
    (h : (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self) = .fail e) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 (self := self) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : aspis_prover.state_only_entropy.Profile21SourceExpander)
    (h : (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self) = .div) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 (self := self) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue043

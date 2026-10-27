import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue042
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.m31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32)) : Result ((core.result.Result aspis_core.field.M31
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_entropy.Profile21SourceExpander) := do
  let (self1, pending_return) := out
  match pending_return with
  | none =>
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted,
      self1)
  | some r => ok (r, self1)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : aspis_prover.state_only_entropy.Profile21SourceExpander) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.m31 (self := self) =
      (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32 >>= fun out => continueAfter (self := self) out) := by
  rw [aspis_prover.state_only_entropy.Profile21SourceExpander.m31]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32))
    (h : (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32) = .ok out) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.m31 (self := self) = continueAfter (self := self) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (e : Error)
    (h : (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32) = .fail e) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.m31 (self := self) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : aspis_prover.state_only_entropy.Profile21SourceExpander)
    (h : (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32) = .div) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.m31 (self := self) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue042

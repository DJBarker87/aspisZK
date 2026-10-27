import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee005
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.Profile21SourceExpander.qm31` (callee `aspis_prover.state_only_entropy.Profile21SourceExpander.m31`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.Profile21SourceExpander) :
  ∃ next, aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 (self := self) =
    (aspis_prover.state_only_entropy.Profile21SourceExpander.m31 self >>= next) := by
  unfold aspis_prover.state_only_entropy.Profile21SourceExpander.qm31
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee005

import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee009
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.Commitment.fill_opening` (callee `host_commitment.fill_opening_values`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) :
  ∃ next, host_commitment.Commitment.fill_opening (self := self) (u := u) (out := out) =
    (host_commitment.fill_opening_values self u out.values 0#usize >>= next) := by
  unfold host_commitment.Commitment.fill_opening
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee009

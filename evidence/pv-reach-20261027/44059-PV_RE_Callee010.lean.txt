import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee010
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.EncodingDomain.new` (callee `host_commitment.domain_points`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
   :
  ∃ next, host_commitment.EncodingDomain.new  =
    (host_commitment.domain_points >>= next) := by
  unfold host_commitment.EncodingDomain.new
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee010

import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix011
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.opening_lane_values` (op76).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) :
  ∃ next, @host_commitment.opening_lane_values _ _ word u =
    (aspis_core.r0.domain.FibreIndex.get u >>= next) := by
  unfold host_commitment.opening_lane_values
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix011

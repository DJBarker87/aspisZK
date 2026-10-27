import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix036
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.publish_compact` (op242).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (variant : transport.Variant) (p : prover.Publication) :
  ∃ next, @prover.publish_compact _ _ variant p =
    (compact.PROOF_BYTES >>= next) := by
  unfold prover.publish_compact
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix036

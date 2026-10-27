import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix017
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.extra_claims` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
  ∃ next, @host_semantic.extra_claims _ _ columns variant a b =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_semantic.extra_claims
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix017

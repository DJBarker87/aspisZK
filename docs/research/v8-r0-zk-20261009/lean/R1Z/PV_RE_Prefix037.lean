import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix037
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.semantic_error` (op256).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (e : r1_wire.Error) :
  ∃ next, @prover.semantic_error _ _ e =
    (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole >>= next) := by
  unfold prover.semantic_error
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix037

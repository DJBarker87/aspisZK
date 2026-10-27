import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix008
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.EncodingDomain.encode` (op32).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (message : Array T 1024#usize) :
  ∃ next, @host_commitment.EncodingDomain.encode _ _ T aspis_corer0scalarCodeFieldInst self message =
    (alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new (alloc.vec.Vec
      T)) 4#usize >>= next) := by
  unfold host_commitment.EncodingDomain.encode
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix008

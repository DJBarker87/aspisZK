import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix025
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.prove_sumcheck` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8) (initial_claim : aspis_core.field.QM31) (oracle : T1) :
  ∃ next, @host_sumcheck.prove_sumcheck _ _ H T1 aspis_coredigestDigest32Inst OracleInst transcript output initial_claim oracle =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_sumcheck.prove_sumcheck
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix025

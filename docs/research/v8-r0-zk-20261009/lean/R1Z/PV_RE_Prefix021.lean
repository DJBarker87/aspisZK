import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix021
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.zc_rows` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
  ∃ next, @host_semantic.zc_rows _ _ H aspis_coredigestDigest32Inst transcript bytes =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_semantic.zc_rows
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix021

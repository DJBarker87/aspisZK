import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee022
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.semantic_row` (callee `host_wire.record`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (row : Std.U8) (payload : Slice Std.U8) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
  ∃ next, host_semantic.semantic_row (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (row := row) (payload := payload) (transcript := transcript) (bytes := bytes) =
    (host_wire.record row payload >>= next) := by
  unfold host_semantic.semantic_row
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee022

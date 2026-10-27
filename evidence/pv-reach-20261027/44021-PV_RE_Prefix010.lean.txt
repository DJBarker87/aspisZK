import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix010
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.encode_commitment_words_loop1.body` (op34).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (words : alloc.vec.Vec host_commitment.Word) (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word
  aspis_core.r0.Error)) :
  ∃ next, @host_commitment.encode_commitment_words_loop1.body _ _ words encoded =
    (alloc.vec.Vec.is_empty Global encoded >>= next) := by
  unfold host_commitment.encode_commitment_words_loop1.body
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix010

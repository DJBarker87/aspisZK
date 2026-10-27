import R1Z.PDict_WireError
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ErrorConsumer
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- Actual error continuation: only ActivePole is retryable. All payload-bearing
wire rejections remain Semantic; no successful-body equation is supplied. -/
theorem semantic_error (ops : ExternalFuns) (e : r1_wire.Error) :
    @prover.semantic_error _ (PDict_WireError.selected ops) e =
      .ok (match e with
        | .ActivePole => verifier.Error.Rejected
        | _ => verifier.Error.Semantic) := by
  unfold prover.semantic_error
  rw [PDict_WireError.installed]
  cases e <;> rfl

#print axioms semantic_error
end R1Z.PDict_ErrorConsumer

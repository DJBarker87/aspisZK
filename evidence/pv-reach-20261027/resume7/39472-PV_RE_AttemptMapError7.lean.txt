import R1Z.PV_RE_AttemptContext7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AttemptMapError7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes]
theorem attempt_to_maperror (D : ExternalFuns) (pub : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (secret : Secrets) (store : Store)
    (bytes : alloc.vec.Vec U8)
    (serialization : D.op226 pub = .ok (.Ok bytes))
 :
    ∃ next, @prover.prove_masked_attempt _ D pub compiled variant hash secret store =
      (D.op12
        prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        (.Ok bytes) () >>= next) := by
  letI : ExternalFuns := D
  unfold prover.prove_masked_attempt
  have call_eq :
      @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes _ D pub =
      D.op226 pub := rfl
  rw [call_eq, serialization]
  exact ⟨_,rfl⟩
#print axioms attempt_to_maperror
end R1Z.PV_RE_AttemptMapError7

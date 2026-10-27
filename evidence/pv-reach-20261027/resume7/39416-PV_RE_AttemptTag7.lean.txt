import R1Z.PV_RE_AttemptContext7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AttemptTag7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7
variable [ExternalTypes]
theorem attempt_to_tag (D : ExternalFuns) (pub : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (secret : Secrets) (store : Store)
    (bytes : alloc.vec.Vec U8) (digest : Array U8 32#usize)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (context : Context)
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context) :
    ∃ next, @prover.prove_masked_attempt _ D pub compiled variant hash secret store =
      (D.op234 variant >>= next) := by
  letI : ExternalFuns := D
  unfold prover.prove_masked_attempt
  have call_eq :
      @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes _ D pub =
      D.op226 pub := rfl
  rw [call_eq, serialization]
  change ∃ next, (D.op12
    prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
    (.Ok bytes) () >>= _) = _
  rw [map_error]
  change ∃ next, (hash (publicFrame bytes) >>= _) = _
  rw [first_hash]
  change ∃ next, (D.op115 digest secret.mask_nonce >>= _) = _
  rw [context_prefix]
  exact ⟨_,rfl⟩
#print axioms attempt_to_tag
end R1Z.PV_RE_AttemptTag7

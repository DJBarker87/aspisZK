import R1Z.PV_RE_AttemptBindingHash7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AttemptReserve7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
theorem attempt_to_reserve (D : ExternalFuns) (pub : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (secret : Secrets) (store : Store)
    (bytes : alloc.vec.Vec U8) (digest : Array U8 32#usize)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (context : Context)
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context)
    (tag : U8) (tag_prefix : D.op234 variant = .ok tag)
    (encoded : Array U8 81#usize) (encode_prefix : D.op116 context = .ok encoded)
    (binding : Array U8 32#usize)
    (second_hash : hash (bindingFrame bytes tag encoded) = .ok binding) :
    ∃ next, @prover.prove_masked_attempt _ D pub compiled variant hash secret store =
      (@aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        _ D Store
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        secret hash binding context store >>= next) := by
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
  change ∃ next, (D.op234 variant >>= _) = _
  rw [tag_prefix]
  change ∃ next, (D.op116 context >>= _) = _
  rw [encode_prefix]
  change ∃ next, (hash (bindingFrame bytes tag encoded) >>= _) = _
  rw [second_hash]
  unfold prover.prove_masked_with_attempt
  exact ⟨_,rfl⟩
#print axioms attempt_to_reserve
end R1Z.PV_RE_AttemptReserve7

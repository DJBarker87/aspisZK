import R1Z.PDict_FmtRetryComplete
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterIndependent
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- This deliberately divergent unreachable callback is an erasure witness,
not a native interpretation of Debug or Formatter. -/
@[reducible] def erased (ops : ExternalFuns) : ExternalFuns :=
  { ops with op85 := fun _ _ => .div }

/-- Complete source retry execution, including all aborts and machine outcomes,
has no Formatter operation contract. No assumption on op85 is made. -/
theorem retry_erased (ops : ExternalFuns) :
    @prover.retry_attempt _ (erased ops) = @prover.retry_attempt _ ops :=
  PDict_FmtErase.erase_425 ops (erased ops)

/-- Replacing op85 needs no equality premise for any predicate of the complete
retry function. Every input, output and observable interpretation is fixed. -/
theorem property_iff (ops : ExternalFuns)
    (P : (∀ {T : Type},
      core.ops.function.FnMut T Usize (core.result.Result
        aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error) →
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
      aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 →
      transport.Variant → (Slice (Slice U8) → Result (Array U8 32#usize)) →
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → T → Usize →
      Result ((core.result.Result prover.RetriedProof verifier.Error) ×
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)) → Prop) :
    P (@prover.retry_attempt _ (erased ops)) ↔ P (@prover.retry_attempt _ ops) := by
  rw [retry_erased]

#print axioms retry_erased
#print axioms property_iff
end R1Z.PDict_FormatterIndependent

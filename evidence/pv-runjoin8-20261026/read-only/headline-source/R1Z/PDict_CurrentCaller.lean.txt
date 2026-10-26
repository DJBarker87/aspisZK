import R1Z.PDict_CurrentRetention
import R1Z.PDict_ReachCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_CurrentCaller
open Aeneas Aeneas.Std ProverRwFull
open PDict_CodecDictionary (native selected)

/-- The thirteen new selected bodies coexist with the proved seven-field
whole-caller source erasure. Every caller argument and Result outcome is kept. -/
theorem seven_field_caller (base : ExternalTypes)
    (ops other : @ExternalFuns (native base)) :
    @RealR1_client.prove_for_proof_accounts (native base)
      (@PDict_ReachErase.replace (native base) (selected base ops) other) =
    @RealR1_client.prove_for_proof_accounts (native base) (selected base ops) :=
  @PDict_ReachErase.client_8 (native base) (selected base ops) other

/-- Any interpretation of this complete extracted caller can use the erasure;
this theorem does not itself construct the native observer/world RunJoin. -/
theorem caller_property (base : ExternalTypes)
    (ops other : @ExternalFuns (native base))
    (P : (∀ {T0 : Type},
      core.ops.function.FnMut T0 Usize (Array U8 32#usize) →
      @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (native base) →
      @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (native base) →
      (Slice (Slice U8) → Result (Array U8 32#usize)) →
      @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore (native base) → T0 →
      Result ((core.result.Result prover.RetriedProof verifier.Error) ×
        @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore (native base))) → Prop) :
    P (@RealR1_client.prove_for_proof_accounts (native base)
      (@PDict_ReachErase.replace (native base) (selected base ops) other)) ↔
    P (@RealR1_client.prove_for_proof_accounts (native base) (selected base ops)) := by
  rw [seven_field_caller]

#print axioms seven_field_caller
#print axioms caller_property
end R1Z.PDict_CurrentCaller

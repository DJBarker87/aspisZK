import R1Z.PV_W_ProverEntry
import R1Z.PV_W_TypedThreading
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_EntryThreading
open ProverRwFull PV_W_Syntax PV_W_Threading PV_W_TypedEffects PV_W_ProverEntry
open Aeneas.Std
variable [ExternalTypes]
variable {W C : Type}
variable (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice U8) → Aeneas.Std.Result (Array U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)

/-- Exact source entry, including early rejection. The nested
prove_masked_with_attempt/helper interpretations remain explicit obligations;
this theorem does not claim whole-prover native trace correspondence. -/
theorem entry_source (dictionary : ExternalFuns) :
    erase dictionary (maskedAttempt public1 compiled variant hash attempt nonce_store) =
      @prover.prove_masked_attempt _ dictionary public1 compiled variant hash attempt nonce_store :=
  erase_maskedAttempt dictionary public1 compiled variant hash attempt nonce_store

theorem entry_threads (a : Algebra W C Aeneas.Std.Error) (step : W → C → W → Prop)
    (laws : PV_W_TypedThreading.Laws a step) (w : W) :
    Threaded step w
      (eval (interpret a) (maskedAttempt public1 compiled variant hash attempt nonce_store) w).calls
      (eval (interpret a) (maskedAttempt public1 compiled variant hash attempt nonce_store) w).world :=
  eval_valid (interpret a) step (PV_W_TypedThreading.primitive_valid a step laws) _ w

theorem entry_operational (a : Algebra W C Aeneas.Std.Error) (w : W)
    (r : Run W C Aeneas.Std.Error
      ((core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) ×
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
    (executed : Executes (interpret a) (maskedAttempt public1 compiled variant hash attempt nonce_store) w r) :
    eval (interpret a) (maskedAttempt public1 compiled variant hash attempt nonce_store) w = r :=
  execution_sound (interpret a) executed

#print axioms entry_source
#print axioms entry_threads
#print axioms entry_operational
end R1Z.PV_W_EntryThreading

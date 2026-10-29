import R1Z.PV_RunJoin_NativeAuditVariant55
import R1Z.PV_RunJoin_NativeBuildSource55
import R1Z.PV_RunJoin_NativeAuditSource55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeVariantTransport55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultRelation55
open PV_RunJoin_NativeControl55 PV_RunJoin_NativeResult55
variable [ExternalTypes] [ExternalFuns]

theorem complete {A B : Type} (R : A → B → Prop)
    (f : Phase → Result (core.result.Result A verifier.Error))
    (g : Phase → Result (core.result.Result B verifier.Error))

  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
    (step : ∀ p,p.variant=variant → Rel (CoreRel R) (f p) (g p))
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
    Rel (Output R)
      (run f aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store)
      (run g aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store) := by
  simp only [PV_RunJoin_NativeBuildSource55.complete,PV_RunJoin_NativeAuditSource55.complete]
  exact PV_RunJoin_NativeAuditVariant55.complete R f g
    aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant step hash context binding attempt nonce_store

#print axioms complete
end R1Z.PV_RunJoin_NativeVariantTransport55

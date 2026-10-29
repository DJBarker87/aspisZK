import R1Z.PV_RunJoin_NativeAuditContext55
import R1Z.PV_RunJoin_NativeBuildContext55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAuditSource55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
theorem complete {A : Type} (publish : Phase → Result (core.result.Result A verifier.Error))
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
    PV_RunJoin_NativeBuildContext55.run publish aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      public1 compiled variant hash context binding attempt nonce_store=
    PV_RunJoin_NativeAuditContext55.run publish aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      public1 compiled variant hash context binding attempt nonce_store := by
  unfold PV_RunJoin_NativeBuildContext55.run PV_RunJoin_NativeAuditContext55.run PV_RunJoin_NativeAfterAudit55.run
  rfl

#print axioms complete
end R1Z.PV_RunJoin_NativeAuditSource55

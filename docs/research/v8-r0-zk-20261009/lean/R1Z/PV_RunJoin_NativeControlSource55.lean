import R1Z.PV_RunJoin_NativeControl55
import R1Z.PV_RunJoin_ResultBindEq55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeControlSource55
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
attribute [local irreducible] prover.prove_from_semantics host_semantic.build_with_material
attribute [local irreducible] prover.audit_masks prover.fixed_k_column prover.derive_private_salts
attribute [local irreducible] host_commitment.EncodingDomain.new
attribute [local irreducible] aspis_statement.state_only_semantic.state_only_copy_helper_sum
attribute [local irreducible] core.option.Option.Insts.CoreCmpPartialEqOption.eq

theorem complete
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
    prover.prove_masked_with_attempt aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      public1 compiled variant hash context binding attempt nonce_store=
    PV_RunJoin_NativeControl55.run PV_RunJoin_NativeControl55.source
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      public1 compiled variant hash context binding attempt nonce_store := by
  unfold prover.prove_masked_with_attempt PV_RunJoin_NativeControl55.run
  simp only [PV_RunJoin_NativeControl55.source]
  rfl

#print axioms complete
end R1Z.PV_RunJoin_NativeControlSource55

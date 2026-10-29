import R1Z.PV_RunJoin_NativeAttemptControl55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAttemptLaws55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeAttemptControl55
open PV_RunJoin_ResultRelation55 PV_RunJoin_NativeResult55
variable [ExternalTypes] [ExternalFuns]
attribute [local irreducible] prover.prove_masked_with_attempt

theorem execute_literal (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (hash : aspis_core.digest.LegacyHashFn) (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (store : Store) :
    PV_RunJoin_NativePublication55.execute storeInst ⟨public1,compiled,hash,context,binding,attempt,store⟩=
      prover.prove_masked_with_attempt storeInst public1 compiled .S2 hash context binding attempt store := rfl

theorem source
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    prover.prove_masked_attempt public1 compiled .S2 hash attempt nonce_store=
      run (PV_RunJoin_NativePublication55.execute storeInst) public1 compiled hash attempt nonce_store := by
  unfold prover.prove_masked_attempt run
  apply PV_RunJoin_ResultBindEq55.complete
  intro publicResult
  apply PV_RunJoin_ResultBindEq55.complete
  intro publicStatus
  cases publicStatus with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  | Ok publicBytes =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
    apply PV_RunJoin_ResultBindEq55.complete
    intro digest
    apply PV_RunJoin_ResultBindEq55.complete
    intro nonce
    apply PV_RunJoin_ResultBindEq55.complete
    intro context
    try simp only [lift,bind_tc_ok]
    apply PV_RunJoin_ResultBindEq55.complete
    intro tag
    apply PV_RunJoin_ResultBindEq55.complete
    intro encodedContext
    try simp only [lift,bind_tc_ok]
    apply PV_RunJoin_ResultBindEq55.complete
    intro binding
    rw [execute_literal]
    all_goals rfl

theorem relation {A B : Type} (R : A → B → Prop)
    (f : PV_RunJoin_NativePublication55.Input Store → Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × Store))
    (g : PV_RunJoin_NativePublication55.Input Store → Result (core.result.Result (B × prover.MaskedFixtureAudit) verifier.Error × Store))
    (step : ∀ i,Rel (Output R) (f i) (g i))
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    Rel (Output R) (run f public1 compiled hash attempt nonce_store) (run g public1 compiled hash attempt nonce_store) := by
  unfold run
  apply PV_RunJoin_ResultRelation55.same_bind
  intro publicResult
  apply PV_RunJoin_ResultRelation55.same_bind
  intro publicStatus
  cases publicStatus with
  | Err e => exact PV_RunJoin_NativeResult55.error R _ _
  | Ok publicBytes =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro digest
    apply PV_RunJoin_ResultRelation55.same_bind
    intro nonce
    apply PV_RunJoin_ResultRelation55.same_bind
    intro context
    try simp only [lift,bind_tc_ok]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro tag
    apply PV_RunJoin_ResultRelation55.same_bind
    intro encodedContext
    try simp only [lift,bind_tc_ok]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro binding
    exact step _

#print axioms execute_literal
#print axioms source
#print axioms relation
end R1Z.PV_RunJoin_NativeAttemptLaws55

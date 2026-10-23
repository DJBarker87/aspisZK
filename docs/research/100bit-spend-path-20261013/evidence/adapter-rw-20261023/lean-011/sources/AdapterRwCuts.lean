import AdapterRwModel

set_option autoImplicit false
namespace AspisR1.AdapterRw.Cuts
open Aeneas Aeneas.Std Result AdapterRw
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Statement := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1

/-- Invert outer success without discarding native errors, failure or divergence. -/
theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a) = ok out) : ∃ a, m = ok a ∧ f a = ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The SHIPPED observer body extracts to None; no child hypothesis. -/
theorem observer_none (ops : AdapterRw.Ops) : AdapterRw.observer ops = ok none := rfl

/-- Exact verifier call from the SHIPPED first_decoded body, including None.
This is a per-call extraction fact, not a native effect-frame theorem. -/
theorem first_decoded_call (ops : AdapterRw.Ops)
    (p : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicInput proof : Slice U8) (split : Usize) :
    AdapterRw.first_decoded ops p publicInput proof split = (do
      let r ← ops.op12 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        p publicInput proof split () none
      AdapterRw.core.result.Result.map_err
        (BuiltinFnOnce AdapterRw.aspis_r1_cost_probe.verifier.Error PE) r ops.op49) := by
  rfl

elab "head_reduce " h:ident : tactic => do
  let id ← Lean.Elab.Tactic.getFVarId h
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let type ← id.getType
    let args := type.getAppArgs
    unless type.isAppOfArity ``Eq 3 do throwError "not equality"
    let lhs ← Lean.Meta.whnf args[1]!
    if lhs == args[1]! then throwError "head unchanged"
    let next := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.zero]) args[0]! lhs args[2]!
    return [← goal.changeLocalDecl id next]

attribute [local irreducible] AdapterRw.Slice.Insts.CoreCmpPartialEqArray AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption AdapterRw.core.result.Result.map_err AdapterRw.Slice.Insts.CoreCmpPartialEqSlice AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexPrivate_slice_indexSealed AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice AdapterRw.aspis_r1_cost_probe.transport.Variant.tag AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey AdapterRw.SolanaDigest.Insts.CoreCloneClone AdapterRw.SolanaDigest.Insts.CoreMarkerCopy AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 AdapterRw.observer AdapterRw.first_decoded AdapterRw.r1_pool_adapter.PROFILE_BINDING AdapterRw.r1_pool_adapter.RELEASE_BINDING AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING AdapterRw.r1_pool_adapter.PAIR_FOREST_MASTER_SEED AdapterRw.r1_pool_adapter.PAIR_FOREST_LANE_SEED AdapterRw.r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED AdapterRw.r1_pool_adapter.VERIFIER_REGISTRY_SEED AdapterRw.r1_pool_adapter.VERIFIER_ENTRY_SEED AdapterRw.r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED AdapterRw.r1_pool_adapter.VERIFIER_ENTRY_V2_SEED AdapterRw.r1_pool_adapter.readonly_meta_ok AdapterRw.r1_pool_adapter.readonly_buffer_meta_ok AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner AdapterRw.r1_pool_adapter.owned.OwnedAccount.data AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len AdapterRw.r1_pool_adapter.owned.require_readonly_buffer AdapterRw.r1_pool_adapter.owned.require_readonly_account AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts AdapterRw.r1_pool_adapter.owned.require_zero_loop.body AdapterRw.r1_pool_adapter.owned.require_zero_loop AdapterRw.r1_pool_adapter.owned.require_zero AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_10.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_10.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts AdapterRw.r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once AdapterRw.r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError AdapterRw.r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once AdapterRw.r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError AdapterRw.r1_pool_adapter.owned.validate_asq8 AdapterRw.r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once AdapterRw.r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError AdapterRw.r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once AdapterRw.r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError AdapterRw.r1_pool_adapter.owned.stage1_owned AdapterRw.r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once AdapterRw.r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError AdapterRw.r1_pool_adapter.owned.stage2_owned

/-- A successful whole owned TX1 must return a vector whose length equals the
same checkpoint data inspected before decoding. No child output is fabricated. -/
theorem stage1_checkpoint_length (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ account bytes,
      Slice.index_usize accounts 2#usize = ok account ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops account = ok (.Ok bytes) ∧
      alloc.vec.Vec.len checkpoint = Slice.len bytes := by
  unfold AdapterRw.r1_pool_adapter.owned.stage1_owned at accepted
  repeat' first
  | (solve | cases accepted)
  | head_reduce accepted
  | split at accepted
  all_goals trace_state
  all_goals aesop

#print axioms bind_success
#print axioms observer_none
#print axioms first_decoded_call
#print axioms stage1_checkpoint_length
end AspisR1.AdapterRw.Cuts

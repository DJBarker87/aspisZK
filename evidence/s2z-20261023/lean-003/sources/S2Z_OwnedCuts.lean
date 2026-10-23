import AdapterRwCuts

/-! Source-derived value dependencies of the adopted callers. These cuts do
not equip pure Result with a native clock or claim effect-trace equality. -/
set_option autoImplicit false
namespace AspisR1.S2Z.OwnedCuts
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw.Cuts
attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.require_distinct_accounts AdapterRw.r1_pool_adapter.owned.require_readonly_buffer AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint AdapterRw.r1_pool_adapter.owned.OwnedAccount.data AdapterRw.r1_pool_adapter.owned.require_zero AdapterRw.first_decoded

/-- All three statement operations and the actual verifier invocation share
one decoded statement. The encoded prefix and semantic projection cannot be
chosen independently of that statement. Error branches are inverted, not
assumed successful in advance. Source bind order is preserved in the model. -/
theorem first_dependencies (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ publicAccount publicInput statement common encoded semantic selected split,
      Slice.index_usize accounts 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok publicInput) ∧
      ops.op47 publicInput = ok (.Ok statement) ∧
      ops.op21 statement = ok (.Ok ()) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
        statement = ok common ∧
      ops.op24 common.lane_transition.candidate_afterstate = ok (.Ok encoded) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      AdapterRw.first_decoded ops semantic publicInput selected split = ok (.Ok checkpoint) := by
  unfold AdapterRw.r1_pool_adapter.owned.stage1_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

/-- Stage2 reaches the actual tx2 and emitter on the SAME authenticated
statement. Authentication is the extracted full body, not a new Ops stub.
This supplies the two value cuts only; emitter/native effect ordering needs
an interpretation of the explicit source binds. -/
theorem second_dependencies (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot =
      ok (.Ok ())) :
    ∃ validated publicArray selected checkpointInput,
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok validated) ∧
      ops.op22 validated.statement = ok (.Ok publicArray) ∧
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice publicArray) selected checkpointInput () none = ok (.Ok ()) ∧
      ops.op53 validated.statement = ok (.Ok ()) := by
  obtain ⟨v,pa,ca,proof,ck,pub,selected,start,finish,h⟩ := stage2_call ops program accounts data slot accepted
  exact ⟨v,pub,selected,ck,h.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1⟩

#print axioms first_dependencies
#print axioms second_dependencies
end AspisR1.S2Z.OwnedCuts

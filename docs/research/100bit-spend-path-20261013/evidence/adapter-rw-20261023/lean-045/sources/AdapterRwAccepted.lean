import AdapterRwCuts
import AdapterRwConstants
import AdapterRwRanges

set_option autoImplicit false
namespace AspisR1.AdapterRw.Accepted
open Aeneas Aeneas.Std Result
open Cuts

attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  AdapterRw.r1_pool_adapter.owned.require_zero AdapterRw.first_decoded
  AdapterRw.r1_pool_adapter.owned.validate_asq8

/-- Exact TX1 arguments, fixed proof range and length guard, derived from the
WHOLE accepted owned caller. The children are arbitrary, not assumed successful. -/
theorem first_call (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput raw statement semantic selected split,
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok publicInput) ∧
      ops.op47 publicInput = ok (.Ok statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start := 688#usize, «end» := 58295#usize} = ok selected ∧
      AdapterRw.first_decoded ops semantic publicInput selected split = ok (.Ok checkpoint) ∧
      raw.val.length = 58295 := by
  unfold AdapterRw.r1_pool_adapter.owned.stage1_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err,
    Constants.constant_aspis_r1_cost_probe_verifier_PROOF_BYTES,
    Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    Scalar.checked_add_eq 688#usize 57607#usize 58295#usize (by scalar_tac),
    AdapterRw.core.option.Option.ok_or, bind_tc_ok] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

/-- These two shapes are the proofLength/proofSuffix content at the native TX1
call cut. Global site provenance and two-transaction identity are separate. -/
theorem first_proof_shapes (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput raw statement semantic selected split,
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok publicInput) ∧
      ops.op47 publicInput = ok (.Ok statement) ∧
      AdapterRw.first_decoded ops semantic publicInput selected split = ok (.Ok checkpoint) ∧
      selected.val.length = 57607 ∧ raw.val = raw.val.take 688 ++ selected.val := by
  obtain ⟨pa,pu,pub,raw,stmt,semantic,selected,split,hpa,hpu,hr,hpub,hd,_,range,first,length⟩ :=
    first_call ops program accounts data checkpoint accepted
  have shape := Ranges.suffix_exact raw selected 688#usize 58295#usize
    (by scalar_tac) (by simpa using length) range
  exact ⟨pa,pu,pub,raw,stmt,semantic,selected,split,hpa,hpu,hr,hpub,hd,first,
    by simpa using shape.1,by simpa using shape.2⟩

#print axioms first_call
#print axioms first_proof_shapes
end AspisR1.AdapterRw.Accepted

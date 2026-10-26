import AdapterRwCuts
import RPz7_S6CurrentCodecTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentStage1CodecJoin
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Public := AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

theorem first_success (ops : AdapterRw.Ops) (semantic : Public)
    (publicInput proof : Slice U8) (split : Usize) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.first_decoded ops semantic publicInput proof split=ok (.Ok checkpoint)) :
    ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      semantic publicInput proof split () none=ok (.Ok checkpoint) := by
  rw [AspisR1.AdapterRw.Cuts.first_decoded_call] at accepted
  obtain ⟨reply,called,returned⟩ := AspisR1.AdapterRw.Cuts.bind_success _ _ _ accepted
  cases reply with
  | Ok value =>
    simp only [AdapterRw.core.result.Result.map_err] at returned
    cases returned
    exact called
  | Err error =>
    simp only [AdapterRw.core.result.Result.map_err] at returned
    obtain ⟨mapped,_,bad⟩ := AspisR1.AdapterRw.Cuts.bind_success _ _ _ returned
    cases bad

/-- Codec/public reuse at the actual extracted CURRENT owned stage1 body.
Every decoder, encoder and verifier success below comes from the one accepted
parent call and its concrete codec slots. External SDK effects and the verifier
body installation are separate; no native state/abort transport is claimed. -/
theorem accepted_stage1 (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops) program accounts data=ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput proofInput statement semantic selected split start finish encoded,
      Slice.index_usize accounts 0#usize=ok proofAccount ∧
      Slice.index_usize accounts 1#usize=ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (install ops) proofAccount=ok (.Ok proofInput) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (install ops) publicAccount=ok (.Ok publicInput) ∧
      decode publicInput=ok (.Ok statement) ∧
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 publicInput=
        ok (.Ok (toPoolV1PairForestTerminalStatementV1 statement)) ∧
      encode statement=ok (.Ok encoded) ∧ encoded.val=publicInput.val ∧
      (install ops).op21 statement=ok (.Ok ()) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofInput {start:=start,«end»:=finish}=ok selected ∧
      (install ops).op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops))
        semantic publicInput selected split () none=ok (.Ok checkpoint) ∧
      Slice.len proofInput=finish := by
  obtain ⟨proofAccount,publicAccount,publicInput,proofInput,statement,semantic,selected,split,start,finish,
    hproof,hpublic,hproofdata,hpublicdata,hdecode,hvalid,hsemantic,hrange,hfirst,hlength⟩ :=
      AspisR1.AdapterRw.Cuts.stage1_call (install ops) program accounts data checkpoint accepted
  obtain ⟨encoded,hencode,hbytes⟩ := accepted_inverse publicInput statement hdecode
  exact ⟨proofAccount,publicAccount,publicInput,proofInput,statement,semantic,selected,split,start,finish,encoded,
    hproof,hpublic,hproofdata,hpublicdata,hdecode,decode_success publicInput statement hdecode,
    hencode,hbytes,hvalid,hsemantic,hrange,
    first_success (install ops) semantic publicInput selected split checkpoint hfirst,hlength⟩

#print axioms first_success
#print axioms accepted_stage1
end AspisS6CurrentStage1CodecJoin

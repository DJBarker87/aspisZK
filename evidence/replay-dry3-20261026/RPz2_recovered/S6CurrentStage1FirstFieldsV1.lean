import S6CurrentFirstInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentStage1FirstFields
open AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
/-- ONE accepted actual owned source call supplies both account reads and the
concrete decoder/codec/first connection, preserving the actual slices and None.
No separately successful child or input-identity premise is assumed. -/
theorem accepted_stage1 (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (AspisS6CurrentFirstInstallation.install ops vops) program accounts data=ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput proofInput statement semantic selected split start finish encoded,
      Slice.index_usize accounts 0#usize=ok proofAccount ∧
      Slice.index_usize accounts 1#usize=ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (AspisS6CurrentFirstInstallation.install ops vops) proofAccount=ok (.Ok proofInput) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (AspisS6CurrentFirstInstallation.install ops vops) publicAccount=ok (.Ok publicInput) ∧
      decode publicInput=ok (.Ok statement) ∧
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 publicInput=
        ok (.Ok (toPoolV1PairForestTerminalStatementV1 statement)) ∧
      encode statement=ok (.Ok encoded) ∧ encoded.val=publicInput.val ∧
      (AspisS6CurrentFirstInstallation.install ops vops).op21 statement=ok (.Ok ()) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofInput {start:=start,«end»:=finish}=ok selected ∧
      (AspisS6CurrentFirstInstallation.install ops vops).op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (AspisS6CurrentFirstInstallation.install ops vops))
        semantic publicInput selected split () none=ok (.Ok checkpoint) ∧
      Slice.len proofInput=finish ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
        (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (AspisS6CurrentFirstInstallation.install ops vops)))
        (fun error => ops.op44 (fromError error)) publicInput selected split=ok (.Ok checkpoint) := by
  obtain ⟨proofAccount,publicAccount,publicInput,proofInput,statement,semantic,selected,split,start,finish,encoded,
    hproof,hpublic,hproofdata,hpublicdata,hdecode,hnative,hencode,hbytes,hvalid,hsemantic,hrange,hcall,hlength⟩ :=
    AspisS6CurrentStage1CodecJoin.accepted_stage1 {ops with op10:=current vops}
      program accounts data checkpoint accepted
  have htx := current_success vops
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (AspisS6CurrentFirstInstallation.install ops vops))
    semantic publicInput selected split () checkpoint hcall
  have selection := selected_public statement
  rw [hsemantic] at selection
  have samePublic := Result.ok.inj selection
  rw [samePublic] at htx
  refine ⟨proofAccount,publicAccount,publicInput,proofInput,statement,semantic,selected,split,start,finish,encoded,
    hproof,hpublic,hproofdata,hpublicdata,hdecode,hnative,hencode,hbytes,hvalid,hsemantic,hrange,hcall,hlength,?_⟩
  unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
  rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ hnative]
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer
    AspisR1CurrentCaller.FirstComposition.currentTx1
  simp only [bind_tc_ok,Option.map_none,htx,
    AspisR1PublicPreparation.core.result.Result.map_err]

#print axioms accepted_stage1
end AspisS6CurrentStage1FirstFields

import S6CurrentFirstInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentStage1FirstJoin
open AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier

/-- The actual current owned parent supplies decoding, all public1880 bytes and
THIS current first/tx1 checkpoint. No independently successful child is added. -/
theorem accepted_stage1 (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops) program accounts data=ok (.Ok checkpoint)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisS6CurrentCodecInstallation.Statement) (encoded : Array U8 1880#usize),
      AspisS6CurrentCodecInstallation.decode bytes=ok (.Ok statement) ∧
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes=
        ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)) ∧
      AspisS6CurrentCodecInstallation.encode statement=ok (.Ok encoded) ∧ encoded.val=bytes.val ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
        (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
        (fun error => ops.op44 (fromError error)) bytes proof split=ok (.Ok checkpoint) := by
  obtain ⟨proofAccount,publicAccount,bytes,proofInput,statement,semantic,proof,split,start,finish,encoded,
    hproof,hpublic,hproofdata,hpublicdata,hdecode,hnative,hencode,hbytes,hvalid,hsemantic,hrange,hcall,hlength⟩ :=
    AspisS6CurrentStage1CodecJoin.accepted_stage1 {ops with op10:=current vops} program accounts data checkpoint accepted
  have htx := current_success vops
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops))
    semantic bytes proof split () checkpoint hcall
  have selection := selected_public statement
  rw [hsemantic] at selection
  have samePublic := Result.ok.inj selection
  rw [samePublic] at htx
  refine ⟨bytes,proof,split,statement,encoded,hdecode,hnative,hencode,hbytes,?_⟩
  unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
  rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ hnative]
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer
    AspisR1CurrentCaller.FirstComposition.currentTx1
  simp only [bind_tc_ok,Option.map_none,htx,
    AspisR1PublicPreparation.core.result.Result.map_err]

#print axioms accepted_stage1
end AspisS6CurrentStage1FirstJoin

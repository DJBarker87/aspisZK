import S6SdkSourceCutTypesV1
import S6CurrentStage1FirstFieldsV1
import CurrentCompactTx1ReachabilityV1
import AdapterRwAccepted
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkSourceCutReuse
open Aeneas Aeneas.Std Result
open AspisR1 S2W_NativeConsolidation MultiproofConeCanonical
open AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier

/-- The retained byte representation is injective on complete source bytes. -/
theorem bytes_injective : Function.Injective bytesOf := by
  apply List.map_injective
  intro a b h
  apply UScalar.eq_of_val_eq
  exact congrArg Fin.val h

/-- The whole source call determines the actual public/proof/split and selected
semantic input on ANY published SourceCuts witnesses for that same call. The
published f.semantic need not carry a semantic-selection equation. No such
equation or equality to a reconstructed statement is assumed here. -/
theorem same_inputs (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts accounts2 : Slice AdapterRw.Cuts.Account) (data : Slice U8)
    (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)
      program accounts data = ok (.Ok saved))
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (install ops vops) accounts accounts2 saved f s) :
    ∃ semantic,
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok semantic ∧
      AdapterRw.first_decoded (install ops vops) semantic f.pub f.proof f.split = ok (.Ok saved) ∧
      f.split = AspisR1CurrentCaller.compact.SPLIT := by
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ip,iu,rp,ru,dc,selected,ranged,called,length⟩ :=
    AdapterRw.Accepted.first_call (install ops vops) program accounts data saved accepted
  have samePa := Result.ok.inj (ip.symm.trans cuts.proof1Index)
  have samePu := Result.ok.inj (iu.symm.trans cuts.public1Index)
  subst pa
  subst pu
  have sameRaw := core.result.Result.Ok.inj (Result.ok.inj (rp.symm.trans cuts.proof1Read))
  have samePub := core.result.Result.Ok.inj (Result.ok.inj (ru.symm.trans cuts.public1Read))
  subst raw
  subst pub
  have sameStatement := core.result.Result.Ok.inj (Result.ok.inj (dc.symm.trans cuts.decode))
  subst statement
  have shape := AdapterRw.Ranges.suffix_exact f.raw proof 688#usize 58295#usize
    (by scalar_tac) (by simpa using length) ranged
  have mapped : bytesOf f.raw.val = (bytesOf f.raw.val).take 688 ++ bytesOf proof.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape.2
  have proofBytes := List.append_cancel_left (mapped.symm.trans cuts.firstSuffix)
  have proofEqual : proof = f.proof := Subtype.ext (bytes_injective proofBytes)
  subst proof
  have tx := current_success vops _ semantic f.pub f.proof split () saved
    (AspisS6CurrentStage1CodecJoin.first_success (install ops vops) semantic f.pub f.proof split saved called)
  have cutTx := current_success vops _ f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success (install ops vops) f.semantic f.pub f.proof f.split saved cuts.first)
  have sourceSplit := (AspisR1CurrentCaller.Tx1Reachability.tx1_success vops _ _
    f.pub f.proof split () saved tx).1
  have cutSplit := (AspisR1CurrentCaller.Tx1Reachability.tx1_success vops _ _
    f.pub f.proof f.split () saved cutTx).1
  have sameSplit : split = f.split := sourceSplit.trans cutSplit.symm
  subst split
  exact ⟨semantic,selected,called,cutSplit⟩

/-- The S6 decoder/reuse result holds on the EXACT published enclosing caller
cuts, rather than independently chosen successful first-call witnesses. -/
theorem source_cut_reuse (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts accounts2 : Slice AdapterRw.Cuts.Account) (data : Slice U8)
    (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)
      program accounts data = ok (.Ok saved))
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (install ops vops) accounts accounts2 saved f s) :
    ∃ encoded,
      decode f.pub = ok (.Ok f.statement) ∧
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 f.pub =
        ok (.Ok (toPoolV1PairForestTerminalStatementV1 f.statement)) ∧
      encode f.statement = ok (.Ok encoded) ∧ encoded.val = f.pub.val ∧
      f.split = AspisR1CurrentCaller.compact.SPLIT ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
        (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
        (fun error => ops.op44 (fromError error)) f.pub f.proof f.split = ok (.Ok saved) := by
  obtain ⟨semantic,selected,called,split⟩ := same_inputs ops vops program accounts accounts2 data saved accepted f s cuts
  have decoded : decode f.pub = ok (.Ok f.statement) := cuts.decode
  have native := decode_success f.pub f.statement decoded
  obtain ⟨encoded,encodedCall,bytes⟩ := accepted_inverse f.pub f.statement decoded
  have tx := current_success vops _ semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success (install ops vops) semantic f.pub f.proof f.split saved called)
  have selection := selected_public f.statement
  rw [selected] at selection
  have samePublic := Result.ok.inj selection
  rw [samePublic] at tx
  refine ⟨encoded,decoded,native,encodedCall,bytes,split,?_⟩
  unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
  rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ native]
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer
    AspisR1CurrentCaller.FirstComposition.currentTx1
  simp only [bind_tc_ok,Option.map_none,tx,AspisR1PublicPreparation.core.result.Result.map_err]

#print axioms bytes_injective
#print axioms same_inputs
#print axioms source_cut_reuse
end AspisS6SdkSourceCutReuse

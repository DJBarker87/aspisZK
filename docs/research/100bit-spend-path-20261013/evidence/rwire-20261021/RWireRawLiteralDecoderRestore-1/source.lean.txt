import RawLiteralDecoderDensity
import RWireRawLiteralDecoderCompletion
import LiteralWordAgreement

/-! Completing the erased decoder also completes the enriched literal decoder,
provided the words already committed by this round agree. The condition is
component-wise: future commitment words are not assumed known. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawLiteralDecoderRestore
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

theorem decodes_and_follows (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (prior : List (Bytes × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1) (Q : Nat)
    (hQ : firstReads emptyTable (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable
          (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior))
    (n : Nat) (hn : n < 33) (raw : Bytes)
    (hfirst : firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) = some raw)
    (choose : RawLiteralDecoderDensity.WordChoice) (W : Words)
    (hwords :
      let tr := RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior
      let T := tableBefore emptyTable tr raw
      let w := choose raw T (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)) (LiteralTranscript.erase (pf n))
      w.c1 = W.c1 ∧ (2 ≤ n → w.c2 = W.c2) ∧ (30 ≤ n → w.final = W.final)) :
    let tr := RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior
    let T := tableBefore emptyTable tr raw
    ∃ own pend g,
      RawLiteralDecoderDensity.decode choose pub raw T = some (own,pend,g) ∧
      bfollow g (traceFrom tr raw) own pend T =
        some (enrichPrefix W ((LiteralByteProtocol.protocol decoder).transcript H pub pf n),
          enrichMessage W (pf n),(LiteralByteProtocol.protocol decoder).chal H pub pf n) := by
  dsimp only at hwords ⊢
  obtain ⟨own,pend,g,hd,hf⟩ := RWireRawLiteralDecoderCompletion.decodes_erased_and_follows
    decoder draw H pub pf hvalid prior hprior Q hQ hout n hn raw hfirst
  let tr := RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior
  let T := tableBefore emptyTable tr raw
  let P := LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)
  let m := LiteralTranscript.erase (pf n)
  let f := RawLiteralDecoderDensity.restore (choose raw T)
  refine ⟨own,pend,fun x as => f (g x as),?_,?_⟩
  · unfold RawLiteralDecoderDensity.decode
    rw [hd]
    rfl
  · rw [BackgroundOutputMap.bfollow_map,hf]
    apply congrArg some
    change RawLiteralDecoderDensity.restore (choose raw T)
      (P,m,(LiteralByteProtocol.protocol decoder).chal H pub pf n) = _
    have hr : P.round = n := by
      dsimp only [P]
      rw [LiteralTranscript.erasePrefix_round,FS2.transcript_round]
    unfold RawLiteralDecoderDensity.restore
    dsimp only
    rw [hr]
    exact LiteralWordAgreement.actual_output decoder H pub pf (choose raw T P m) W n
      (fun i hi => hvalid i (by omega)) hwords.1 hwords.2.1 hwords.2.2

#print axioms decodes_and_follows

end AspisR1.RWireRawLiteralDecoderRestore
end

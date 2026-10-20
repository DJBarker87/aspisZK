import RawUnifiedDecoder
import RWireLiteralLegacyDecoderCompletion

/-! The actual all-33-round literal verifier has a raw-byte background decoder.
The result reconstructs its erased transcript and exact challenge, outside the
same raw collision event and with no bound on adversarial input length. Literal
committed-word metadata is the next enrichment bridge. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawLiteralDecoderCompletion
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralLegacyRun CanonicalAddressEmbedding

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

theorem chain_firstCell_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i)) (n : Nat) (hn : n < 33) :
    firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) =
      (firstCell (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n)).map Addr.toBytes := by
  change firstCell (ProgramSamplerMap.map Addr.toBytes (LiteralTranscript.samp n
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) (pf n))) = _
  rw [firstCell_map]
  unfold LiteralTranscript.samp
  rw [erased_transcript_eq decoder H pub pf hvalid n (by omega),message_eq pf hvalid n hn]
  rfl

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I) (ha : firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [firstCell,Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [firstCell,Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

theorem decodes_erased_and_follows (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (prior : List (Bytes × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1) (Q : Nat)
    (hQ : firstReads emptyTable (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable
          (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior))
    (n : Nat) (hn : n < 33) (raw : Bytes)
    (hfirst : firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) = some raw) :
    let tr := RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior
    let T := tableBefore emptyTable tr raw
    ∃ own pend g,
      RawUnifiedDecoder.decode SelectedTranscriptParams.params
        (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub raw T =
          some (own,pend,g) ∧
      bfollow g (traceFrom tr raw) own pend T =
        some (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n),
          LiteralTranscript.erase (pf n),(LiteralByteProtocol.protocol decoder).chal H pub pf n) := by
  dsimp only
  rw [chain_firstCell_eq decoder H pub pf hvalid n hn] at hfirst
  cases hf : firstCell (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n) with
  | none => simp [hf] at hfirst
  | some a =>
      have he : a.toBytes = raw := by simpa [hf] using hfirst
      subst raw
      have hmem := firstCell_mem (fun b => H b.toBytes)
        (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n) a hf
      obtain ⟨q,hq,heq⟩ := List.mem_map.mp hmem
      have ha : CanonicalByteAddress.Canonical a := by
        have hc := RawBoundedProgram.labels_eval CanonicalByteAddress.Canonical
          (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n).toProgram
          (LiteralLegacyVerifierTrace.chain_canonical (fun b => H b.toBytes) pub (proof pf) n)
          (fun b => H b.toBytes) q hq
        simpa [heq] using hc
      have hlegacy := RWireLiteralLegacyDecoderCompletion.decodes_and_follows decoder draw H pub pf
        hvalid prior hprior Q hQ hout n hn a hf
      have hraw := RawUnifiedDecoder.decodes_and_follows_of_legacy SelectedTranscriptParams.params
        (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub ⟨a,ha⟩
        (tableBefore emptyTable (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) a.toBytes)
        (traceFrom (RWireLiteralLegacyDecoderCompletion.rawTrace decoder draw H pub pf prior) a.toBytes)
        (legacyProtocol.transcript (fun b => H b.toBytes) pub (proof pf) n,
          legacyProtocol.msg (proof pf) n,
          legacyProtocol.chal (fun b => H b.toBytes) pub (proof pf) n) hlegacy
      rw [erased_transcript_eq decoder H pub pf hvalid n (by omega),message_eq pf hvalid n hn]
      have hc : (LiteralByteProtocol.protocol decoder).chal H pub pf n =
          legacyProtocol.chal (fun b => H b.toBytes) pub (proof pf) n :=
        congrArg Prod.snd (chain_eval_eq decoder H pub pf hvalid n hn)
      rw [hc]
      exact hraw

#print axioms chain_firstCell_eq
#print axioms decodes_erased_and_follows
#print axioms firstCell_map
#print axioms firstCell_mem
end AspisR1.RWireRawLiteralDecoderCompletion
end

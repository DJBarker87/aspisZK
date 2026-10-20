import LiteralLegacyVerifierTrace
import RWireRawBoundedCollision
import R1UnifiedTotalCase

/-! Reuse the complete legacy 33-row decoder on the actual literal-byte
verifier trace after an arbitrary consistent raw prover prefix. Both legacy
collision exclusions and the query budget follow from the single raw event.
No adversarial input-length bound or assumed decoder-completion theorem is
introduced. The decoder output is the erased transcript; literal-word
enrichment and raw background-sampler density remain subsequent bridges. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireLiteralLegacyDecoderCompletion

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralLegacyRun

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I) (ha : firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [firstCell, Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [firstCell, Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

def rawTrace (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (prior : List (Bytes × State)) : List (Bytes × State) :=
  prior ++ (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder) draw pub pf)).1

theorem decodes_and_follows (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (prior : List (Bytes × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (Q : Nat)
    (hQ : firstReads emptyTable (rawTrace decoder draw H pub pf prior) ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable (rawTrace decoder draw H pub pf prior))
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n) = some a) :
    let tr := rawTrace decoder draw H pub pf prior
    let T := RawBoundedTrace.table L (tableBefore emptyTable tr a.toBytes)
    ∃ own pend g,
      UnifiedDecoder.decode SelectedTranscriptParams.params
        (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T =
          some (own,pend,g) ∧
      bfollow g (RawBoundedTrace.trace L (traceFrom tr a.toBytes)) own pend T =
        some (legacyProtocol.transcript (fun b => H b.toBytes) pub (proof pf) n,
          legacyProtocol.msg (proof pf) n,
          legacyProtocol.chal (fun b => H b.toBytes) pub (proof pf) n) := by
  dsimp only
  let Hb : Addr L → State := fun b => H b.toBytes
  let tr := rawTrace decoder draw H pub pf prior
  let bp := RawBoundedTrace.trace L prior
  let P := RawBoundedProgram.readTrace bp (proof pf)
  let V := FS2.verifier legacyProtocol (fun _ _ => true)
  have hcons : ∀ q ∈ tr, q.2 = H q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hp | hv
    · exact hprior q hp
    · exact FS.eval_consistent H _ q hv
  have hP : eval Hb P = (bp,proof pf) :=
    RawBoundedProgram.eval_readTrace Hb bp (proof pf)
      (RawBoundedTrace.trace_consistent L H prior hprior)
  have htrace : (eval Hb (FS.experiment P V pub)).1 = RawBoundedTrace.trace L tr := by
    rw [FS.experiment_eval, hP]
    change bp ++ (eval Hb (V pub (proof pf))).1 =
      RawBoundedTrace.trace L
        (prior ++ (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder) draw pub pf)).1)
    rw [RawBoundedProgram.trace_append,
      LiteralLegacyVerifierTrace.restricted_trace_eq decoder draw (fun _ _ => true) H pub pf hvalid]
  have hbQ : firstReads emptyTable (eval Hb (FS.experiment P V pub)).1 ≤ Q := by
    rw [htrace]
    exact (RawBoundedTrace.firstReads_trace_le L tr).trans hQ
  have hbout : ¬ hitsBad (badColl SelectedTranscriptParams.params Q) emptyTable
      (eval Hb (FS.experiment P V pub)).1 := by
    rw [htrace]
    exact RWireRawBoundedCollision.no_duplex_collision SelectedTranscriptParams.params
      H tr Q hcons hQ hout
  have hbtail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Q) emptyTable
      (eval Hb (FS.experiment P V pub)).1 := by
    rw [htrace]
    exact RWireRawBoundedCollision.no_tail_collision SelectedTranscriptParams.params.iv
      H tr Q hcons hQ hout
  have hpub : pub.pubBytes.length < 2^32 := by
    have hf := pub.initFits
    change 75 + pub.pubBytes.length ≤ 131072 at hf
    omega
  let m0 : BytesMessage := ⟨PublicInitFrame.emptyRecord, by decide⟩
  have hfirstP : firstCell (legacyProtocol.chain Hb pub (eval Hb P).2 n) = some a := by
    rw [hP]
    exact hfirst
  obtain ⟨own,pend,g,hdecode,hfollow⟩ :=
    UnifiedTotalCase.decodes_and_follows SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      (fun _ _ => (none : Option Unit)) (fun _ _ => true) Hb pub P hpub
      (by intro i hi; rfl) m0 rfl Q hbQ hbout hbtail n hn a hfirstP
  have haRead := firstCell_mem Hb (legacyProtocol.chain Hb pub (proof pf) n) a hfirst
  obtain ⟨q,hq,he⟩ := List.mem_map.mp haRead
  have hcan : CanonicalByteAddress.Canonical a := by
    have hc := RawBoundedProgram.labels_eval CanonicalByteAddress.Canonical
      (legacyProtocol.chain Hb pub (proof pf) n).toProgram
      (LiteralLegacyVerifierTrace.chain_canonical Hb pub (proof pf) n) Hb q hq
    simpa [he] using hc
  have ht := RawBoundedTrace.tableBefore_trace L emptyTable tr ⟨a,hcan⟩
  rw [RawBoundedTrace.table_empty] at ht
  have hs := RawBoundedTrace.traceFrom_trace L tr ⟨a,hcan⟩
  change UnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a
      (tableBefore emptyTable (eval Hb (FS.experiment P V pub)).1 a) =
      some (own,pend,g) at hdecode
  change bfollow g (traceFrom (eval Hb (FS.experiment P V pub)).1 a) own pend
      (tableBefore emptyTable (eval Hb (FS.experiment P V pub)).1 a) =
      some (legacyProtocol.transcript Hb pub (eval Hb P).2 n,
        legacyProtocol.msg (eval Hb P).2 n,
        legacyProtocol.chal Hb pub (eval Hb P).2 n) at hfollow
  rw [htrace] at hdecode hfollow
  rw [hP] at hfollow
  rw [ht] at hdecode hfollow
  rw [hs] at hfollow
  exact ⟨own,pend,g,hdecode,hfollow⟩

#print axioms decodes_and_follows
#print axioms firstCell_mem
end AspisR1.RWireLiteralLegacyDecoderCompletion
end

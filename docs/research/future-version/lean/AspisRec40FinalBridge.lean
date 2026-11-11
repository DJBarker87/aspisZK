import AspisRec40FinalBridgeStatement
import AspisRec40FinalAddr
import AspisRec40FinalLegacy
import RWireRawBoundedCollision
import R1BackgroundOutputMap

/-! W4 proved: the byte-to-address bridge for rows 33 to 39,
`FinalBridgeStatement.DecodesAndFollows40` (the second worker's compiled
statement, unchanged).

Copy of R1's byte chain for rows below 33
(`RWireLiteralLegacyDecoderCompletion.decodes_and_follows`,
`RWireRawLiteralDecoderCompletion.decodes_erased_and_follows`,
`RWireRawLiteralDecoderRestore.decodes_and_follows`) for the final component:
* the byte trace restricted to canonical addresses is the 40-row
  address-level run after the restricted prior trace
  (`FinalLegacy.restricted_trace_eq40`); R1's raw collision event gives R1's
  two address-level exclusions and the budget (`RWireRawBoundedCollision`);
* row n's first cell is row n's absorb frame (`FinalLegacy.chain_firstCell_eq40`,
  `legacy_firstCell`), a canonical address;
* at the address level the statement is selected, the component decodes and
  follows to row n's actual erased output (`FinalAddr.decodes_and_follows`:
  W1, W2, the follow);
* the byte decoder `FinalByte.fin n` is that component at canonical inputs
  (`atCanonical_of_component`, `RawBackgroundCompletion.bfollow_eq`), and its
  restore with the chosen words `W` gives the enriched prefix and message
  (`FinalLegacy.actual_prefix40`, `message_restore`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalBridge
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 LiteralLegacyRun
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

abbrev L := SelectedTranscriptParams.L
abbrev p := SelectedTranscriptParams.params

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

theorem decodes_and_follows40 : FinalBridgeStatement.DecodesAndFollows40 := by
  intro decoder draw H pub pf hvalid hlate htag prior hprior Q hQ hout n hlo hhi raw hfirst W
  dsimp only
  intro hwords
  have hv : FinalLegacy.Valid40 pf := ⟨hvalid, hlate⟩
  let Hb : Addr L → State := fun b => H b.toBytes
  let tr := FinalBridgeStatement.rawTrace40 decoder draw H pub pf prior
  let ext := fun (_ : UnifiedSampler.Public L) (_ : Table (Addr L) State) => (none : Option Unit)
  let dold := fun (_ : UnifiedSampler.Prefix LiteralTranscript.BytesMessage
    AspisWideTower.WideExact L) (_ : TranscriptView.Message LiteralTranscript.BytesMessage) => true
  let π := proof pf
  let bp := RawBoundedTrace.trace L prior
  have hcons : ∀ q ∈ tr, q.2 = H q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hp | hvq
    · exact hprior q hp
    · exact FS.eval_consistent H _ q hvq
  have htrace : RawBoundedTrace.trace L tr =
      AspisRec40.FinalRun.trace p FinalAddr.hD ext dold Hb pub π.1 π.2 bp := by
    change RawBoundedTrace.trace L (prior ++ _) = bp ++ _
    rw [RawBoundedProgram.trace_append,
      FinalLegacy.restricted_trace_eq40 decoder draw ext dold H pub pf hv]
  have hbQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p FinalAddr.hD ext dold Hb pub π.1 π.2 bp) ≤ Q := by
    rw [← htrace]
    exact (RawBoundedTrace.firstReads_trace_le L tr).trans hQ
  have hbout : ¬ hitsBad (badColl p Q) emptyTable
      (AspisRec40.FinalRun.trace p FinalAddr.hD ext dold Hb pub π.1 π.2 bp) := by
    rw [← htrace]
    exact RWireRawBoundedCollision.no_duplex_collision p H tr Q hcons hQ hout
  have hbtail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Q) emptyTable
      (AspisRec40.FinalRun.trace p FinalAddr.hD ext dold Hb pub π.1 π.2 bp) := by
    rw [← htrace]
    exact RWireRawBoundedCollision.no_tail_collision p.iv H tr Q hcons hQ hout
  have hpub : pub.pubBytes.length < 2^32 := by
    have hf := pub.initFits
    change 75 + pub.pubBytes.length ≤ 131072 at hf
    omega
  have hprior' : ∀ q ∈ bp, q.2 = Hb q.1 := RawBoundedTrace.trace_consistent L H prior hprior
  -- row n's first cell
  let a := UnifiedSteps.address p FinalAddr.hD Hb pub π.1 π.2 n
  have hleg : firstCell (legacyProtocol.chain Hb pub π n) = some a :=
    FinalLegacy.legacy_firstCell Hb pub π n (by omega) (by omega) (by omega)
  rw [FinalLegacy.chain_firstCell_eq40 decoder H pub pf hv n hhi, hleg] at hfirst
  have hraw : a.toBytes = raw := by simpa using hfirst
  subst hraw
  have hcan : CanonicalByteAddress.Canonical a := by
    have hmem := firstCell_mem Hb (legacyProtocol.chain Hb pub π n) a hleg
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hmem
    have hc := RawBoundedProgram.labels_eval CanonicalByteAddress.Canonical
      (legacyProtocol.chain Hb pub π n).toProgram
      (LiteralLegacyVerifierTrace.chain_canonical Hb pub π n) Hb q hq
    simpa [he] using hc
  -- the address level
  obtain ⟨hsel, own, pend, g, hcomp, hfol⟩ := FinalAddr.decodes_and_follows ext dold Hb pub π.1 π.2
    bp hprior' hpub htag Q hbQ hbout hbtail n hlo hhi
  have ht := RawBoundedTrace.tableBefore_trace L emptyTable tr ⟨a, hcan⟩
  rw [RawBoundedTrace.table_empty] at ht
  have hs := RawBoundedTrace.traceFrom_trace L tr ⟨a, hcan⟩
  change tableBefore emptyTable (RawBoundedTrace.trace L tr) a =
    RawBoundedTrace.table L (tableBefore emptyTable tr a.toBytes) at ht
  change traceFrom (RawBoundedTrace.trace L tr) a =
    RawBoundedTrace.trace L (traceFrom tr a.toBytes) at hs
  rw [← htrace, ht] at hsel hcomp hfol
  rw [hs] at hfol
  -- the byte decoder
  let T := tableBefore emptyTable tr a.toBytes
  let hg := AspisRows40.Final.component_good p pub n a hcan (RawBoundedTrace.table L T)
    own pend g hcomp
  refine ⟨RawBackgroundCompletion.own own hg.1, RawBackgroundCompletion.pending pend hg.2,
    fun x xs => RawLiteralDecoderDensity.restore (LiteralTableWordChoiceBin.choose a.toBytes T)
      (g x xs), ?_, ?_⟩
  · have hdec : CanonicalRawTrace.decode L a.toBytes = some ⟨a, hcan⟩ :=
      (CanonicalRawTrace.decode_iff L a.toBytes ⟨a, hcan⟩).2 rfl
    have hselb : RawPublicSelectionLift.select L (AspisRows40.FinalByte.select n) a.toBytes T =
        some pub := by
      simp only [RawPublicSelectionLift.select, hdec, Option.bind_some]
      exact hsel
    unfold AspisRows40.FinalByte.fin
    rw [hselb, Option.bind_some, hdec, Option.bind_some,
      AspisRows40.FinalByte.atCanonical_of_component pub n ⟨a, hcan⟩ T own pend g hcomp]
    rfl
  · rw [BackgroundOutputMap.bfollow_map, RawBackgroundCompletion.bfollow_eq]
    rw [hfol]
    apply congrArg some
    -- the address-level output is the erased output of the literal run
    have hT : UnifiedRun.transcript p FinalAddr.hD Hb pub π.1 π.2 n =
        LiteralTranscript.erasePrefix
          ((AspisRows40.Protocol.protocol decoder).transcript H pub pf n) := by
      rw [AspisRows40.Protocol.transcript_eq,
        FinalLegacy.erased_transcript_eq40 decoder H pub pf hv n (by omega),
        legacyProtocol, UnifiedProtocol.transcript_eq]
    have hM : UnifiedRun.message π.1 π.2 n = LiteralTranscript.erase (pf n) :=
      (FinalLegacy.message_eq40 pf hv n hhi).symm
    have hC : UnifiedRun.challenge p FinalAddr.hD Hb pub π.1 π.2 n =
        (AspisRows40.Protocol.protocol decoder).chal H pub pf n := by
      unfold FS2.Protocol.chal
      rw [AspisRows40.Protocol.chain_eq, FinalLegacy.chain_eval_eq40 decoder H pub pf hv n hhi]
      change _ = (eval Hb (legacyProtocol.chain Hb pub π n).toProgram).2
      rw [legacyProtocol, UnifiedProtocol.chain_eq]
      rfl
    rw [hT, hM, hC]
    unfold RawLiteralDecoderDensity.restore
    dsimp only
    rw [hwords]
    have hr : (LiteralTranscript.erasePrefix
        ((AspisRows40.Protocol.protocol decoder).transcript H pub pf n)).round = n := by
      rw [LiteralTranscript.erasePrefix_round, FS2.transcript_round]
    rw [hr, FinalLegacy.message_restore W n (pf n) (Or.inr ⟨hlo, hlate n hlo hhi⟩),
      AspisRows40.Protocol.transcript_eq,
      FinalLegacy.actual_prefix40 decoder H pub pf hv W n (by omega)]

#print axioms decodes_and_follows40

end AspisRec40.FinalBridge
end
